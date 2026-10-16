use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
#[allow(unused_imports)]
use curve25519_dalek::traits::{Identity, MultiscalarMul, VartimeMultiscalarMul};
use hmac_transcript::HmacTranscript;
use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "parallel")]
use crate::util_msm::chunked_vartime_multiscalar_mul;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use inner_product_proof::prove_ecp;
use inner_product_proof::prove_ipa;
use std::iter;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use transcript::TranscriptProtocol;

static PROVER_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

/// An entry point for creating a R1CS proof.
///
/// The lifecycle of a `Prover` is as follows. The proving code
/// commits high-level variables and their blinding factors `(v, v_blinding)`,
/// `Prover` generates commitments, adds them to the transcript and returns
/// the corresponding variables.
///
/// After all variables are committed, the proving code calls `finalize_inputs`,
/// which consumes `Prover` and returns `ProverCS`.
/// The proving code then allocates low-level variables and adds constraints to the `ProverCS`.
///
/// When all constraints are added, the proving code calls `prove`
/// on the instance of the constraint system and receives the complete proof.
pub struct Prover<'a, 'b> {
    /// Number of high-level variables
    m: u64,

    /// Constraint system implementation
    cs: ProverCS<'a, 'b>,
}

/// A [`ConstraintSystem`] implementation for use by the prover.
pub struct ProverCS<'a, 'b> {
    transcript: &'a mut HmacTranscript,
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    constraints: Vec<LinearCombination>,
    a_L: Vec<Scalar>,
    a_R: Vec<Scalar>,
    a_O: Vec<Scalar>,
    v: Vec<Scalar>,
    v_blinding: Scalar,
}

/// Overwrite secrets with null bytes when they go out of scope.
impl<'a, 'b> Drop for ProverCS<'a, 'b> {
    fn drop(&mut self) {
        self.v.clear();
        self.v_blinding.zeroize();

        for e in self.a_L.iter_mut() {
            e.zeroize();
        }
        for e in self.a_R.iter_mut() {
            e.zeroize();
        }
        for e in self.a_O.iter_mut() {
            e.zeroize();
        }
    }
}

impl<'a, 'b> ConstraintSystem for ProverCS<'a, 'b> {
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        // Synthesize the assignments for l,r,o
        let l = self.eval(&left);
        let r = self.eval(&right);
        let o = l * r;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::ONE));
        right.terms.push((r_var, -Scalar::ONE));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, assign_fn: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let (l, r, o) = assign_fn()?;

        // Create variables for l,r,o ...
        let l_var = Variable::MultiplierLeft(self.a_L.len());
        let r_var = Variable::MultiplierRight(self.a_R.len());
        let o_var = Variable::MultiplierOutput(self.a_O.len());
        // ... and assign them
        self.a_L.push(l);
        self.a_R.push(r);
        self.a_O.push(o);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // (e.g. that variables are valid, that the linear combination evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Prover<'a, 'b> {
    /// Construct an empty constraint system with specified external
    /// input variables.
    ///
    /// # Inputs
    ///
    /// The `bp_gens` and `pc_gens` are generators for Bulletproofs
    /// and for the Pedersen commitments, respectively.  The
    /// [`BulletproofGens`] should have `gens_capacity` greater than
    /// the number of multiplication constraints that will eventually
    /// be added into the constraint system.
    ///
    /// The `transcript` parameter is a Merlin proof transcript.  The
    /// `ProverCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`ProverCS::prove`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `ProverCS` before proving is complete.
    ///
    /// # Returns
    ///
    /// Returns a new `Prover` instance.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut HmacTranscript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Prover {
            m: 0,
            cs: ProverCS {
                pc_gens,
                bp_gens,
                transcript,
                v: Vec::new(),
                v_blinding: Scalar::ZERO,
                constraints: Vec::new(),
                a_L: Vec::new(),
                a_R: Vec::new(),
                a_O: Vec::new(),
            },
        }
    }

    ///
    pub fn commit_vec(
        &mut self,
        v: &[Scalar],
        v_blinding: Scalar,
        k_original: usize,
    ) -> (CompressedRistretto, Vec<Variable>) {
        let start_index = self.m as usize;
        let n_padded = v.len();

        // Safety check
        assert!(k_original <= n_padded);

        // Update prover state
        self.m += n_padded as u64;
        for &v_i in v.iter() {
            self.cs.v.push(v_i);
        }
        self.cs.v_blinding = v_blinding;

        #[cfg(feature = "parallel")]
        let V = {
            let scalars: Vec<Scalar> = iter::once(v_blinding).chain(v[0..k_original].iter().copied()).collect();
            let points: Vec<RistrettoPoint> = iter::once(self.cs.pc_gens.B_blinding).chain(self.cs.bp_gens.G(k_original, 1).copied()).collect();
            chunked_vartime_multiscalar_mul(&scalars, &points).compress()
        };
        #[cfg(not(feature = "parallel"))]
        let V = RistrettoPoint::vartime_multiscalar_mul(
            iter::once(&v_blinding).chain(v[0..k_original].iter()),
            iter::once(&self.cs.pc_gens.B_blinding).chain(self.cs.bp_gens.G(k_original, 1)),
        )
        .compress();

        // Add the commitment to the transcript
        self.cs.transcript.commit_point(b"V", &V);

        // Build committed variables for the FULL range
        let vars: Vec<Variable> = (start_index..start_index + n_padded)
            .map(|i| Variable::Committed(i))
            .collect();

        (V, vars)
    }

    /// Consume the `Prover`, provide the `ConstraintSystem` implementation to the closure,
    /// and produce a proof.
    pub fn finalize_inputs(self) -> ProverCS<'a, 'b> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.cs.transcript.commit_u64(b"m", self.m);
        self.cs
    }
}

impl<'a, 'b> ProverCS<'a, 'b> {
    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>) {
        let n = self.a_L.len();
        let m = self.v.len();

        let mut wL = vec![Scalar::ZERO; n];
        let mut wR = vec![Scalar::ZERO; n];
        let mut wO = vec![Scalar::ZERO; n];
        let mut wV = vec![Scalar::ZERO; m];

        let mut exp_z = *z;
        for lc in self.constraints.iter() {
            for (var, coeff) in &lc.terms {
                match var {
                    Variable::MultiplierLeft(i) => {
                        wL[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierRight(i) => {
                        wR[*i] += exp_z * coeff;
                    }
                    Variable::MultiplierOutput(i) => {
                        wO[*i] += exp_z * coeff;
                    }
                    Variable::Committed(i) => {
                        wV[*i] -= exp_z * coeff;
                    }
                    Variable::One() => {
                        // The prover doesn't need to handle constant terms
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV)
    }

    fn eval(&self, lc: &LinearCombination) -> Scalar {
        lc.terms
            .iter()
            .map(|(var, coeff)| {
                coeff
                    * match var {
                        Variable::MultiplierLeft(i) => self.a_L[*i],
                        Variable::MultiplierRight(i) => self.a_R[*i],
                        Variable::MultiplierOutput(i) => self.a_O[*i],
                        Variable::Committed(i) => self.v[*i],
                        Variable::One() => Scalar::ONE,
                    }
            })
            .sum()
    }

    pub fn prove(
        mut self,
        C1_prime: &[RistrettoPoint],
        C2_prime: &[RistrettoPoint],
        r_prime: Scalar,
        k_fold: usize,
        num_rounds: usize,
        D1_prime: Option<&[RistrettoPoint]>,
        D2_prime: Option<&[RistrettoPoint]>,
        r_prime2: Option<Scalar>,
        alphas: Option<&[Scalar]>,
        D1_raw: Option<&[RistrettoPoint]>,
        D2_raw: Option<&[RistrettoPoint]>,
        e_challenge: Option<&[Scalar]>,
        block_size: usize,
    ) -> Result<R1CSProof, R1CSError> {
        use inner_product_proof::inner_product;
        use rand::thread_rng;
        use std::iter;
        use util;

        let n = self.a_L.len();
        let k = self.v.len();

        if self.bp_gens.gens_capacity < k {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let gens = self.bp_gens.share(0);

        let _do_print = std::env::var("VERBOSE").ok().filter(|v| v == "1" || v.eq_ignore_ascii_case("true")).is_some()&& !PROVER_TIMING_PRINTED.swap(true, Ordering::SeqCst);
        let _t_total = Instant::now();

        // 0. Transcript & RNG
        let _tp = Instant::now();
        let mut rng = {
            use rand::RngCore;
            use rand_chacha::ChaCha20Rng;
            use rand::SeedableRng;

            let witness_seed = self.transcript.witness_rng_seed(self.v_blinding.as_bytes());
            let mut os_bytes = [0u8; 32];

            if std::env::var("MAYA_DETERMINISTIC").ok().as_deref() != Some("1") {
                thread_rng().fill_bytes(&mut os_bytes);
            }

            let mut seed = [0u8; 32];
            for i in 0..32 {
                seed[i] = witness_seed[i] ^ os_bytes[i];
            }
            ChaCha20Rng::from_seed(seed)
        };
        if _do_print {
            eprintln!(
                "  [0] Witness RNG (HMAC seed): {:>7.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 1. Circuit Commitment
        let _tp = Instant::now();  
        let i_blinding = Scalar::random(&mut rng);
        let o_blinding = Scalar::random(&mut rng);
        let s_blinding = Scalar::random(&mut rng);

        let mut s_L = Vec::with_capacity(n);
        let mut s_R = Vec::with_capacity(n);
        for _ in 0..n {
            s_L.push(Scalar::random(&mut rng));
            s_R.push(Scalar::random(&mut rng));
        }

        #[cfg(feature = "parallel")]
        let (A_I, A_O, S) = {
            let a_L = &self.a_L;
            let a_R = &self.a_R;
            let a_O = &self.a_O;
            let b_blind = self.pc_gens.B_blinding;
            let g_pts: Vec<RistrettoPoint> = gens.G(n).cloned().collect();
            let h_pts: Vec<RistrettoPoint> = gens.H(n).cloned().collect();
            let ((a_i, a_o), s) = rayon::join(
                || {
                    rayon::join(
                        || {
                            let scalars: Vec<Scalar> = iter::once(i_blinding)
                                .chain(a_L.iter().copied())
                                .chain(a_R.iter().copied())
                                .collect();
                            let points: Vec<RistrettoPoint> = iter::once(b_blind)
                                .chain(g_pts.iter().copied())
                                .chain(h_pts.iter().copied())
                                .collect();
                            crate::util_msm::chunked_vartime_multiscalar_mul(&scalars, &points).compress()
                        },
                        || {
                            let scalars: Vec<Scalar> = iter::once(o_blinding)
                                .chain(a_O.iter().copied())
                                .collect();
                            let points: Vec<RistrettoPoint> = iter::once(b_blind)
                                .chain(g_pts.iter().copied())
                                .collect();
                            crate::util_msm::chunked_vartime_multiscalar_mul(&scalars, &points).compress()
                        },
                    )
                },
                || {
                    let scalars: Vec<Scalar> = iter::once(s_blinding)
                        .chain(s_L.iter().copied())
                        .chain(s_R.iter().copied())
                        .collect();
                    let points: Vec<RistrettoPoint> = iter::once(b_blind)
                        .chain(g_pts.iter().copied())
                        .chain(h_pts.iter().copied())
                        .collect();
                    crate::util_msm::chunked_vartime_multiscalar_mul(&scalars, &points).compress()
                },
            );
            (a_i, a_o, s)
        };
        #[cfg(not(feature = "parallel"))]
        let (A_I, A_O, S) = {
            let a_i = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&i_blinding)
                    .chain(self.a_L.iter())
                    .chain(self.a_R.iter()),
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n))
                    .chain(gens.H(n)),
            )
            .compress();
            let a_o = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&o_blinding).chain(self.a_O.iter()),
                iter::once(&self.pc_gens.B_blinding).chain(gens.G(n)),
            )
            .compress();
            let s = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&s_blinding).chain(s_L.iter()).chain(s_R.iter()),
                iter::once(&self.pc_gens.B_blinding)
                    .chain(gens.G(n))
                    .chain(gens.H(n)),
            )
            .compress();
            (a_i, a_o, s)
        };

        self.transcript.commit_point(b"A_I", &A_I);
        self.transcript.commit_point(b"A_O", &A_O);
        self.transcript.commit_point(b"S", &S);
        if _do_print {
            eprintln!(
                "  [1] Circuit commitment (A_I,A_O,S):      {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 2. Polynomials
        let _tp = Instant::now();
        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        let (wL, wR, wO, wV) = self.flattened_constraints(&z);

        let y_inv = y.invert();
        let exp_y_inv: Vec<Scalar> = util::exp_iter(y_inv).take(k).collect();
        let exp_y_vec: Vec<Scalar> = util::exp_iter(y).take(k).collect();

        let mut l_poly = util::VecPoly3::zero(n);
        let mut r_poly = util::VecPoly3::zero(n);

        #[cfg(feature = "parallel")]
        {
            let results: Vec<(Scalar, Scalar, Scalar, Scalar, Scalar, Scalar)> = (0..n)
                .into_par_iter()
                .map(|i| {
                    let l1 = self.a_L[i] + exp_y_inv[i] * wR[i];
                    let l2 = self.a_O[i];
                    let l3 = s_L[i];
                    let r0 = wO[i] - exp_y_vec[i];
                    let r1 = exp_y_vec[i] * self.a_R[i] + wL[i];
                    let r3 = exp_y_vec[i] * s_R[i];
                    (l1, l2, l3, r0, r1, r3)
                })
                .collect();
            for (i, (l1, l2, l3, r0, r1, r3)) in results.into_iter().enumerate() {
                l_poly.1[i] = l1;
                l_poly.2[i] = l2;
                l_poly.3[i] = l3;
                r_poly.0[i] = r0;
                r_poly.1[i] = r1;
                r_poly.3[i] = r3;
            }
        }
        #[cfg(not(feature = "parallel"))]
        {
            for i in 0..n {
                l_poly.1[i] = self.a_L[i] + exp_y_inv[i] * wR[i];
                l_poly.2[i] = self.a_O[i];
                l_poly.3[i] = s_L[i];

                r_poly.0[i] = wO[i] - exp_y_vec[i];
                r_poly.1[i] = exp_y_vec[i] * self.a_R[i] + wL[i];
                r_poly.3[i] = exp_y_vec[i] * s_R[i];
            }
        }

        let t_poly = util::VecPoly3::special_inner_product(&l_poly, &r_poly);
        if _do_print {
            eprintln!(
                "  [2] Polynomial construction (l,r,t):     {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now(); 
        let t_blindings = [
            Scalar::random(&mut rng), 
            Scalar::random(&mut rng), 
            Scalar::random(&mut rng),
            Scalar::random(&mut rng), 
            Scalar::random(&mut rng), 
        ];

        let t_2_blinding = Scalar::random(&mut rng);
        let t_2: Scalar = wV.iter().zip(self.v.iter()).map(|(c, v)| c * v).sum();

        #[cfg(feature = "parallel")]
        let (T_1, T_2, T_3, T_4, T_5, T_6) = {
            let pc = &self.pc_gens;
            let (((t1, t3), (t4, t5)), (t6, t2_commit)) = rayon::join(
                || {
                    rayon::join(
                        || {
                            rayon::join(
                                || pc.commit(t_poly.t1, t_blindings[0]).compress(),
                                || pc.commit(t_poly.t3, t_blindings[1]).compress(),
                            )
                        },
                        || {
                            rayon::join(
                                || pc.commit(t_poly.t4, t_blindings[2]).compress(),
                                || pc.commit(t_poly.t5, t_blindings[3]).compress(),
                            )
                        },
                    )
                },
                || {
                    rayon::join(
                        || pc.commit(t_poly.t6, t_blindings[4]).compress(),
                        || pc.commit(t_2, t_2_blinding).compress(),
                    )
                },
            );
            (t1, t2_commit, t3, t4, t5, t6)
        };
        #[cfg(not(feature = "parallel"))]
        let (T_1, T_2, T_3, T_4, T_5, T_6) = {
            let t1 = self.pc_gens.commit(t_poly.t1, t_blindings[0]).compress();
            let t3 = self.pc_gens.commit(t_poly.t3, t_blindings[1]).compress();
            let t4 = self.pc_gens.commit(t_poly.t4, t_blindings[2]).compress();
            let t5 = self.pc_gens.commit(t_poly.t5, t_blindings[3]).compress();
            let t6 = self.pc_gens.commit(t_poly.t6, t_blindings[4]).compress();
            let t2_commit = self.pc_gens.commit(t_2, t_2_blinding).compress();
            (t1, t2_commit, t3, t4, t5, t6)
        };

        self.transcript.commit_point(b"T_1", &T_1);
        self.transcript.commit_point(b"T_3", &T_3);
        self.transcript.commit_point(b"T_4", &T_4);
        self.transcript.commit_point(b"T_5", &T_5);
        self.transcript.commit_point(b"T_6", &T_6);
        self.transcript.commit_point(b"T_2", &T_2);
        if _do_print {
            eprintln!(
                "  [3] T commitments (T_1..T_6):   {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now();
        let x = self.transcript.challenge_scalar(b"x");

        let t_x = t_poly.eval(x);
        let t_x_blinding = util::Poly6 {
            t1: t_blindings[0],
            t2: t_2_blinding,
            t3: t_blindings[1],
            t4: t_blindings[2],
            t5: t_blindings[3],
            t6: t_blindings[4],
        }
        .eval(x);

        let mut l_vec = l_poly.eval(x);
        let mut r_vec = r_poly.eval(x);

        l_vec.resize(k, Scalar::ZERO);
        r_vec.resize(k, Scalar::ZERO);

        for i in n..k {
            r_vec[i] = -exp_y_vec[i];
        }

        let e_blinding = x * (i_blinding + x * (o_blinding + x * s_blinding));

        self.transcript.commit_scalar(b"t_x", &t_x);
        self.transcript
            .commit_scalar(b"t_x_blinding", &t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &e_blinding);
        if _do_print {
            eprintln!(
                "  [3.1] T commitments (t_x, e_blinding, t_x_blinding):   {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 4. Consistency Setup
        let _tp = Instant::now();
        let s_bl_prime = Scalar::random(&mut rng);
        let rnd = Scalar::random(&mut rng);
        let k_original = C1_prime.len();

        let mut s_L_prime = Vec::with_capacity(k);

        for _ in 0..k_original {
            s_L_prime.push(Scalar::random(&mut rng));
        }

        #[cfg(feature = "parallel")]
        let (S_prime, S1_prime, S2_prime) = {
            let b_blinding = self.pc_gens.B_blinding;
            let b_pt = self.pc_gens.B;
            let f_pt = self.pc_gens.F;
            let g_pts: Vec<RistrettoPoint> = gens.G(k_original).cloned().collect();
            let sl = &s_L_prime[0..k_original];

            let sp_scalars: Vec<Scalar> = iter::once(s_bl_prime).chain(sl.iter().copied()).collect();
            let sp_points: Vec<RistrettoPoint> = iter::once(b_blinding).chain(g_pts.iter().copied()).collect();
            let s_pr = crate::util_msm::chunked_vartime_multiscalar_mul(&sp_scalars, &sp_points).compress();

            let s1_scalars: Vec<Scalar> = iter::once(rnd).chain(sl.iter().copied()).collect();
            let s1_points: Vec<RistrettoPoint> = iter::once(b_pt).chain(C1_prime.iter().copied()).collect();
            let s1_pr = crate::util_msm::chunked_vartime_multiscalar_mul(&s1_scalars, &s1_points).compress();

            let s2_scalars: Vec<Scalar> = iter::once(rnd).chain(sl.iter().copied()).collect();
            let s2_points: Vec<RistrettoPoint> = iter::once(f_pt).chain(C2_prime.iter().copied()).collect();
            let s2_pr = crate::util_msm::chunked_vartime_multiscalar_mul(&s2_scalars, &s2_points).compress();

            (s_pr, s1_pr, s2_pr)
        };
        #[cfg(not(feature = "parallel"))]
        let (S_prime, S1_prime, S2_prime) = {
            let s_pr = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&s_bl_prime).chain(s_L_prime[0..k_original].iter()),
                iter::once(&self.pc_gens.B_blinding).chain(gens.G(k_original)),
            )
            .compress();
            let s1_pr = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&rnd).chain(s_L_prime[0..k_original].iter()),
                iter::once(&self.pc_gens.B).chain(C1_prime.iter()),
            )
            .compress();
            let s2_pr = RistrettoPoint::vartime_multiscalar_mul(
                iter::once(&rnd).chain(s_L_prime[0..k_original].iter()),
                iter::once(&self.pc_gens.F).chain(C2_prime.iter()),
            )
            .compress();
            (s_pr, s1_pr, s2_pr)
        };

        if _do_print {
            eprintln!(
                "  [4] Consistency setup (S',S1',S2'):   {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // Dual-group consistency commitments (per-voter alpha: one alpha_beta per block).
          let dual_group_active = D1_prime.is_some() && D2_prime.is_some()
            && r_prime2.is_some() && alphas.is_some()
            && D1_raw.is_some() && D2_raw.is_some() && e_challenge.is_some();

        let mut y2   = Scalar::ZERO;
        let mut betas: Vec<Scalar> = Vec::new();
        let (S3_prime, S4_prime) = if dual_group_active {
            let d1 = D1_prime.unwrap();
            let d2 = D2_prime.unwrap();
            let dr1 = D1_raw.unwrap();
            let dr2 = D2_raw.unwrap();
            let e = &e_challenge.unwrap()[0..k_original];
            let num_anchors = alphas.unwrap().len();
            if block_size == 0 || num_anchors * block_size != k_original
                || dr1.len() != k_original || dr2.len() != k_original
            {
                return Err(R1CSError::InputLengthError);
            }
            y2   = Scalar::random(&mut rng);
            betas = (0..num_anchors).map(|_| Scalar::random(&mut rng)).collect();
            let sl = &s_L_prime[0..k_original];

            #[cfg(feature = "parallel")]
            let e_beta: Vec<Scalar> = e.par_iter().enumerate()
                .map(|(i, ei)| ei * betas[i / block_size]).collect();
            #[cfg(not(feature = "parallel"))]
            let e_beta: Vec<Scalar> = e.iter().enumerate()
                .map(|(i, ei)| ei * betas[i / block_size]).collect();

            #[cfg(feature = "parallel")]
            let (s3, s4) = rayon::join(
                || {
                    let s3_scalars: Vec<Scalar> = sl.iter().copied()
                        .chain(iter::once(y2))
                        .chain(e_beta.iter().copied())
                        .collect();
                    let s3_points: Vec<RistrettoPoint> = d1.iter().copied()
                        .chain(iter::once(self.pc_gens.B))
                        .chain(dr1.iter().copied())
                        .collect();
                    crate::util_msm::chunked_vartime_multiscalar_mul(&s3_scalars, &s3_points).compress()
                },
                || {
                    let s4_scalars: Vec<Scalar> = sl.iter().copied()
                        .chain(iter::once(y2))
                        .chain(e_beta.iter().copied())
                        .collect();
                    let s4_points: Vec<RistrettoPoint> = d2.iter().copied()
                        .chain(iter::once(self.pc_gens.F2))
                        .chain(dr2.iter().copied())
                        .collect();
                    crate::util_msm::chunked_vartime_multiscalar_mul(&s4_scalars, &s4_points).compress()
                }
            );

            #[cfg(not(feature = "parallel"))]
            let (s3, s4) = {
                let s3_res = RistrettoPoint::vartime_multiscalar_mul(
                    sl.iter().chain(iter::once(&y2)).chain(e_beta.iter()),
                    d1.iter().chain(iter::once(&self.pc_gens.B)).chain(dr1.iter()),
                ).compress();
                let s4_res = RistrettoPoint::vartime_multiscalar_mul(
                    sl.iter().chain(iter::once(&y2)).chain(e_beta.iter()),
                    d2.iter().chain(iter::once(&self.pc_gens.F2)).chain(dr2.iter()),
                ).compress();
                (s3_res, s4_res)
            };

            (s3, s4)
        } else {
            (
                curve25519_dalek::ristretto::RistrettoPoint::identity().compress(),
                curve25519_dalek::ristretto::RistrettoPoint::identity().compress(),
            )
        };


        let S_Ks: Vec<CompressedRistretto> = betas.iter()
            .map(|b| (self.pc_gens.B * b).compress())
            .collect();

        let _tp = Instant::now();
        let mut lc_poly = util::VecPoly1::zero(k);
        let mut rc_poly = util::VecPoly1::zero(k);

        for _ in k_original..k {
            s_L_prime.push(Scalar::ZERO);
        }
        for i in 0..k {
            lc_poly.0[i] = self.v[i];
            lc_poly.1[i] = s_L_prime[i];
            rc_poly.0[i] = wV[i];
        }

        let tc_poly = lc_poly.inner_product(&rc_poly);
        let t1_bl_prime = Scalar::random(&mut rng);
        let T_1_prime = self.pc_gens.commit(tc_poly.1, t1_bl_prime).compress();
        let tc_bl_poly = util::Poly2(t_2_blinding, t1_bl_prime, Scalar::ZERO);

        self.transcript.commit_point(b"S_prime", &S_prime);
        self.transcript.commit_point(b"T_1_prime", &T_1_prime);
        self.transcript.commit_point(b"S1_prime", &S1_prime);
        self.transcript.commit_point(b"S2_prime", &S2_prime);
        if dual_group_active {
            self.transcript.commit_point(b"S3_prime", &S3_prime);
            self.transcript.commit_point(b"S4_prime", &S4_prime);
            for S_K in &S_Ks {
                self.transcript.commit_point(b"S_K", S_K);
            }
        }

        let x_prime = self.transcript.challenge_scalar(b"x_prime");

        let tc_x = tc_poly.eval(x_prime);
        let tc_x_blinding = tc_bl_poly.eval(x_prime);
        let ec_blinding = self.v_blinding + s_bl_prime * x_prime;
        let r_blinding = r_prime + rnd * x_prime;

        // Dual-group responses
        let (r_blinding2, alpha_blindings) = if dual_group_active {
            let rb2 = r_prime2.unwrap() + y2 * x_prime;
            let ab: Vec<Scalar> = betas.iter().zip(alphas.unwrap().iter())
                .map(|(b, a)| b * x_prime - a)
                .collect();
            (rb2, ab)
        } else {
            (Scalar::ZERO, Vec::new())
        };

        self.transcript.commit_scalar(b"tc_x", &tc_x);
        self.transcript
            .commit_scalar(b"tc_x_blinding", &tc_x_blinding);
        self.transcript.commit_scalar(b"ec_blinding", &ec_blinding);
        self.transcript.commit_scalar(b"r_blinding", &r_blinding);
        if dual_group_active {
            self.transcript.commit_scalar(b"r_blinding2", &r_blinding2);
            for ab in &alpha_blindings {
                self.transcript.commit_scalar(b"alpha_blinding", ab);
            }
        }

        let lc_vec = lc_poly.eval(x_prime);
        let rc_vec = rc_poly.eval(x_prime);
        if _do_print {
            eprintln!(
                "  [4.1] Consistency setup (responses):   {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 5. Aggregation Protocol 

        let t_cross = inner_product(&l_vec[0..k], &rc_vec) + inner_product(&lc_vec, &r_vec[0..k]);

        self.transcript.commit_scalar(b"t_cross", &t_cross);
        let x_ipp = self.transcript.challenge_scalar(b"x_ipp");
        let mut l_agg = Vec::with_capacity(k);
        let mut r_agg = Vec::with_capacity(k);

        for i in 0..k {
            l_agg.push(l_vec[i] + x_ipp * lc_vec[i]);
            r_agg.push(r_vec[i] + x_ipp * rc_vec[i]);
        }

        let w_agg = self.transcript.challenge_scalar(b"w_agg");
        let Q_agg = w_agg * self.pc_gens.B;

        let _tp = Instant::now();
        #[cfg(feature = "parallel")]
        let H_prime: Vec<RistrettoPoint> = {
            let h_vec: Vec<RistrettoPoint> = gens.H(k).cloned().collect();
            h_vec
                .par_iter()
                .zip(exp_y_inv.par_iter())
                .map(|(H_i, exp_i)| H_i * exp_i)
                .collect()
        };
        #[cfg(not(feature = "parallel"))]
        let H_prime: Vec<RistrettoPoint> = gens
            .H(k)
            .zip(exp_y_inv.iter())
            .map(|(H_i, exp_i)| H_i * exp_i)
            .collect();

        if _do_print {
            eprintln!(
                "  [5] Aggregation (H'):     {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }
        let _tp = Instant::now();

        let ipp_proof = prove_ipa::create(
            self.transcript,
            k_fold,
            &self.bp_gens.G_vec[0][0..k],
            &H_prime,
            Q_agg,
            &l_agg,
            &r_agg,
            num_rounds,
        );
        if _do_print {
            eprintln!(
                "  [6] IPA proof (prove_ipa):           {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 6. Batched ECP Protocol
        let _tp = Instant::now();
        let chall_batched_ecp = self.transcript.challenge_scalar(b"chall_batched_ecp");

        let C_agg: Vec<RistrettoPoint> = if dual_group_active {
            let d1 = D1_prime.unwrap();
            let d2 = D2_prime.unwrap();
            let chall_sq = chall_batched_ecp * chall_batched_ecp;
            let chall_cb = chall_sq * chall_batched_ecp;
            #[cfg(feature = "parallel")]
            {
                C1_prime.par_iter().zip(C2_prime.par_iter()).zip(d1.par_iter()).zip(d2.par_iter())
                    .map(|(((c1, c2), d1i), d2i)| RistrettoPoint::vartime_multiscalar_mul(
                        &[Scalar::ONE, chall_batched_ecp, chall_sq, chall_cb],
                        &[*c1, *c2, *d1i, *d2i]))
                    .collect()
            }
            #[cfg(not(feature = "parallel"))]
            {
                C1_prime.iter().zip(C2_prime.iter()).zip(d1.iter()).zip(d2.iter())
                    .map(|(((c1, c2), d1i), d2i)| RistrettoPoint::vartime_multiscalar_mul(
                        &[Scalar::ONE, chall_batched_ecp, chall_sq, chall_cb],
                        &[*c1, *c2, *d1i, *d2i]))
                    .collect()
            }
        } else {
            #[cfg(feature = "parallel")]
            {
                C1_prime.par_iter().zip(C2_prime.par_iter())
                    .map(|(c1, c2)| RistrettoPoint::vartime_multiscalar_mul(
                        &[Scalar::ONE, chall_batched_ecp], &[*c1, *c2]))
                    .collect()
            }
            #[cfg(not(feature = "parallel"))]
            {
                C1_prime.iter().zip(C2_prime.iter())
                    .map(|(c1, c2)| c1 + c2 * chall_batched_ecp)
                    .collect()
            }
        };
        if _do_print {
            eprintln!(
                "  [7] (C_agg):    {:>8.3} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
        }

        let _tp = Instant::now();
        let ecp_batched = prove_ecp::create(
            self.transcript,
            k_fold,
            &self.bp_gens.G_vec[0][0..k],
            &C_agg,
            &lc_vec,
            num_rounds,
        );
        if _do_print {
            eprintln!(
                "  [8] eCP proof (prove_ecp::create):                   {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0
            );
            eprintln!(
                "  [TOTAL prover prove()]:                  {:>7.1} ms",
                _t_total.elapsed().as_secs_f64() * 1000.0
            );
        }

        // 7. Cleanup
        for e in s_L.iter_mut() {
            e.zeroize();
        }
        for e in s_R.iter_mut() {
            e.zeroize();
        }
        for e in s_L_prime.iter_mut() {
            e.zeroize();
        }
        y2.zeroize();
        for b in betas.iter_mut() {
            b.zeroize();
        }

        Ok(R1CSProof {
            A_I,
            A_O,
            S,
            T_1,
            T_2,
            T_3,
            T_4,
            T_5,
            T_6,
            t_x,
            t_x_blinding,
            e_blinding,
            ipp_proof,
            S_prime,
            T_1_prime,
            tc_x,
            tc_x_blinding,
            ec_blinding,
            t_cross,
            S1_prime,
            S2_prime,
            S3_prime,
            S4_prime,
            S_Ks,
            r_blinding,
            r_blinding2,
            alpha_blindings,
            ecp_batched,
        })
    }
}


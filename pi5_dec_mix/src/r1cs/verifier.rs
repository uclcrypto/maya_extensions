#![allow(unused_imports, unused_variables)]
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
#[cfg(not(feature = "parallel"))]
use curve25519_dalek::traits::VartimeMultiscalarMul;

use hmac_transcript::HmacTranscript;

use super::{ConstraintSystem, LinearCombination, R1CSProof, Variable};

use errors::R1CSError;
use generators::{BulletproofGens, PedersenGens};
use transcript::TranscriptProtocol;

#[cfg(feature = "parallel")]
use crate::util_msm::{chunked_optional_multiscalar_mul, chunked_vartime_multiscalar_mul};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

static VERIFIER_TIMING_PRINTED: AtomicBool = AtomicBool::new(false);

/// An entry point for verifying a R1CS proof.
///
/// The lifecycle of a `Verrve25519_dalek::traits::IsIdifier` is as follows. The verifying code
/// provides high-level commitments one by one,
/// `Verifier` adds them to the transcript and returns
/// the corresponding variables.
///
/// After all variables are committed, the verifying code calls `finalize_inputs`,
/// which consumes `Verifier` and returns `VerifierCS`.
/// The verifying code then allocates low-level variables and adds constraints to the `VerifierCS`.
///
/// When all constraints are added, the verifying code calls `verify`
/// on the instance of the constraint system to check the proof.
pub struct Verifier<'a, 'b> {
    /// Number of high-level variables
    m: u64,

    /// Constraint system implementation
    cs: VerifierCS<'a, 'b>,
}

/// A [`ConstraintSystem`] implementation for use by the verifier.
pub struct VerifierCS<'a, 'b> {
    bp_gens: &'b BulletproofGens,
    pc_gens: &'b PedersenGens,
    transcript: &'a mut HmacTranscript,
    constraints: Vec<LinearCombination>,
    /// Records the number of low-level variables allocated in the
    /// constraint system.
    ///
    /// Because the `VerifierCS` only keeps the constraints
    /// themselves, it doesn't record the assignments (they're all
    /// `Missing`), so the `num_vars` isn't kept implicitly in the
    /// variable assignments.
    num_vars: usize,
    V: Vec<CompressedRistretto>,
    num_inputs: usize,
}

impl<'a, 'b> ConstraintSystem for VerifierCS<'a, 'b> {
    fn multiply(
        &mut self,
        mut left: LinearCombination,
        mut right: LinearCombination,
    ) -> (Variable, Variable, Variable) {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        // Constrain l,r,o:
        left.terms.push((l_var, -Scalar::ONE));
        right.terms.push((r_var, -Scalar::ONE));
        self.constrain(left);
        self.constrain(right);

        (l_var, r_var, o_var)
    }

    fn allocate<F>(&mut self, _: F) -> Result<(Variable, Variable, Variable), R1CSError>
    where
        F: FnOnce() -> Result<(Scalar, Scalar, Scalar), R1CSError>,
    {
        let var = self.num_vars;
        self.num_vars += 1;

        // Create variables for l,r,o
        let l_var = Variable::MultiplierLeft(var);
        let r_var = Variable::MultiplierRight(var);
        let o_var = Variable::MultiplierOutput(var);

        Ok((l_var, r_var, o_var))
    }

    fn constrain(&mut self, lc: LinearCombination) {
        // (e.g. that variables are valid, that the linear combination
        // evals to 0 for prover, etc).
        self.constraints.push(lc);
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
        self.transcript.challenge_scalar(label)
    }
}

impl<'a, 'b> Verifier<'a, 'b> {
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
    /// `VerifierCS` holds onto the `&mut Transcript` until it consumes
    /// itself during [`VerifierCS::verify`], releasing its borrow of the
    /// transcript.  This ensures that the transcript cannot be
    /// altered except by the `VerifierCS` before proving is complete.
    ///
    /// The `commitments` parameter is a list of Pedersen commitments
    /// to the external variables for the constraint system.  All
    /// external variables must be passed up-front, so that challenges
    /// produced by [`ConstraintSystem::challenge_scalar`] are bound
    /// to the external variables.
    ///
    /// # Returns
    ///
    /// Returns a tuple `(cs, vars)`.
    ///
    /// The first element is the newly constructed constraint system.
    ///
    /// The second element is a list of [`Variable`]s corresponding to
    /// the external inputs, which can be used to form constraints.
    pub fn new(
        bp_gens: &'b BulletproofGens,
        pc_gens: &'b PedersenGens,
        transcript: &'a mut HmacTranscript,
    ) -> Self {
        transcript.r1cs_domain_sep();

        Verifier {
            m: 0,
            cs: VerifierCS {
                bp_gens,
                pc_gens,
                transcript,
                num_vars: 0,
                V: Vec::new(),
                constraints: Vec::new(),
                num_inputs: 0,
            },
        }
    }

    ///
    pub fn commit_vec(&mut self, commitment: CompressedRistretto, n: usize) -> Vec<Variable> {
        let start_index = self.m as usize;

        self.m += n as u64;
        self.cs.num_inputs = self.m as usize;

        self.cs.V.push(commitment);
        self.cs.transcript.commit_point(b"V", &commitment);

        (start_index..start_index + n)
            .map(|i| Variable::Committed(i))
            .collect()
    }

    /// Consume the `Verifier`, provide the `ConstraintSystem` implementation to the closure,
    /// and verify the proof against the resulting constraint system.
    pub fn finalize_inputs(self) -> VerifierCS<'a, 'b> {
        // Commit a length _suffix_ for the number of high-level variables.
        // We cannot do this in advance because user can commit variables one-by-one,
        // but this suffix provides safe disambiguation because each variable
        // is prefixed with a separate label.
        self.cs.transcript.commit_u64(b"m", self.m);
        self.cs
    }
}

impl<'a, 'b> VerifierCS<'a, 'b> {
    /// Use a challenge, `z`, to flatten the constraints in the
    /// constraint system into vectors used for proving and
    /// verification.
    ///
    /// # Output
    ///
    /// Returns a tuple of
    /// ```text
    /// (wL, wR, wO, wV, wc)
    /// ```
    /// where `w{L,R,O}` is \\( z \cdot z^Q \cdot W_{L,R,O} \\).
    ///
    /// This has the same logic as `ProverCS::flattened_constraints()`
    /// but also computes the constant terms (which the prover skips
    /// because they're not needed to construct the proof).
    fn flattened_constraints(
        &mut self,
        z: &Scalar,
    ) -> (Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, Scalar) {
        let n = self.num_vars;
        let m = self.num_inputs;

        let mut wL = vec![Scalar::ZERO; n];
        let mut wR = vec![Scalar::ZERO; n];
        let mut wO = vec![Scalar::ZERO; n];
        let mut wV = vec![Scalar::ZERO; m];
        let mut wc = Scalar::ZERO;

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
                        wc -= exp_z * coeff;
                    }
                }
            }
            exp_z *= z;
        }

        (wL, wR, wO, wV, wc)
    }

    pub fn verify_pi5(
        mut self,
        proof: &R1CSProof,
        C1_prime: &[CompressedRistretto],
        C2_prime: &[CompressedRistretto],
        c1_raw: &[CompressedRistretto],
        c2_raw: &[CompressedRistretto],
        e_challenge: &[Scalar],
        h_rest: RistrettoPoint,
        alpha_pub: CompressedRistretto,
    ) -> Result<(), R1CSError> {
        use curve25519_dalek::traits::IsIdentity;
        use inner_product_proof::inner_product;
        use std::iter;
        use util;

        let _do_print = std::env::var("VERBOSE").ok().filter(|v| v == "1" || v.eq_ignore_ascii_case("true")).is_some()&& !VERIFIER_TIMING_PRINTED.swap(true, Ordering::SeqCst);
        let _t_total = Instant::now();
        let _tp = Instant::now();

        let n = self.num_vars;
        let padded_n = self.num_inputs;
        let k_fold = proof.ipp_proof.k;
        let pad = padded_n - n;

        if self.bp_gens.gens_capacity < padded_n {
            return Err(R1CSError::InvalidGeneratorsLength);
        }

        let gens = self.bp_gens.share(0);

        // 2. Transcript Interaction
        self.transcript.commit_point(b"A_I", &proof.A_I);
        self.transcript.commit_point(b"A_O", &proof.A_O);
        self.transcript.commit_point(b"S", &proof.S);

        let y = self.transcript.challenge_scalar(b"y");
        let z = self.transcript.challenge_scalar(b"z");

        self.transcript.commit_point(b"T_1", &proof.T_1);
        self.transcript.commit_point(b"T_3", &proof.T_3);
        self.transcript.commit_point(b"T_4", &proof.T_4);
        self.transcript.commit_point(b"T_5", &proof.T_5);
        self.transcript.commit_point(b"T_6", &proof.T_6);
        self.transcript.commit_point(b"T_2", &proof.T_2);

        let x = self.transcript.challenge_scalar(b"x");

        self.transcript.commit_scalar(b"t_x", &proof.t_x);
        self.transcript.commit_scalar(b"t_x_blinding", &proof.t_x_blinding);
        self.transcript.commit_scalar(b"e_blinding", &proof.e_blinding);

        #[cfg(feature = "parallel")]
        let (mut wL, mut wR, mut wO, wV, wc) = self.flattened_constraints(&z);
        #[cfg(not(feature = "parallel"))]
        let (wL, wR, wO, wV, wc) = self.flattened_constraints(&z);

        self.transcript.commit_point(b"S_prime", &proof.S_prime);
        self.transcript.commit_point(b"T_1_prime", &proof.T_1_prime);
        self.transcript.commit_point(b"S1_prime", &proof.S1_prime);
        self.transcript.commit_point(b"S2_prime", &proof.S2_prime);
        self.transcript.commit_point(b"S_K", &proof.S_K);

        let x_prime = self.transcript.challenge_scalar(b"x_prime");

        self.transcript.commit_scalar(b"tc_x", &proof.tc_x);
        self.transcript.commit_scalar(b"tc_x_blinding", &proof.tc_x_blinding);
        self.transcript.commit_scalar(b"ec_blinding", &proof.ec_blinding);
        self.transcript.commit_scalar(b"r_blinding", &proof.r_blinding);
        self.transcript.commit_scalar(b"alpha_blinding", &proof.alpha_blinding);

        self.transcript.commit_scalar(b"t_cross", &proof.t_cross);
        let t_cross = proof.t_cross;

        let x_ipp = self.transcript.challenge_scalar(b"x_ipp");
        let w_agg = self.transcript.challenge_scalar(b"w_agg");

        // 3. Scalar and Point Reconstruction
        let (s_g_cir, s_h_cir, s_Q_cir, s_P_cir, s_U_cir) = proof
            .ipp_proof
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let mut U_points_decompressed_cir: Vec<RistrettoPoint> =
            Vec::with_capacity(proof.ipp_proof.U_vecs.len() * (2 * k_fold - 2));
        for r_idx in 0..proof.ipp_proof.U_vecs.len() {
            for i_list in 0..(2 * k_fold - 2) {
                let pt = proof.ipp_proof.U_vecs[r_idx][i_list]
                    .decompress()
                    .ok_or(R1CSError::VerificationError)?;
                U_points_decompressed_cir.push(pt);
            }
        }

        let y_inv = y.invert();

        #[cfg(feature = "parallel")]
        let y_inv_vec: Vec<Scalar> = {
            let num_threads = rayon::current_num_threads();
            let chunk = (padded_n + num_threads - 1) / num_threads;
            (0..num_threads).into_par_iter()
                .flat_map_iter(|t| {
                    let start = t * chunk;
                    if start >= padded_n { return vec![]; }
                    let end = (start + chunk).min(padded_n);
                    let start_power = {
                        let mut result = Scalar::ONE;
                        let mut base = y_inv;
                        let mut exp = start as u64;
                        while exp > 0 {
                            if (exp & 1) == 1 { result *= base; }
                            base *= base;
                            exp >>= 1;
                        }
                        result
                    };
                    let mut block = Vec::with_capacity(end - start);
                    let mut power = start_power;
                    for _ in start..end {
                        block.push(power);
                        power *= y_inv;
                    }
                    block
                })
                .collect()
        };
        #[cfg(not(feature = "parallel"))]
        let y_inv_vec: Vec<Scalar> = util::exp_iter(y_inv).take(padded_n).collect();

        #[cfg(feature = "parallel")]
        let yneg_wR: Vec<Scalar> = {
            wR.resize(padded_n, Scalar::ZERO);
            wR.par_iter().zip(y_inv_vec.par_iter()).map(|(a, b)| a * b).collect()
        };
        #[cfg(not(feature = "parallel"))]
        let yneg_wR: Vec<Scalar> = wR
            .into_iter()
            .zip(y_inv_vec.iter())
            .map(|(wRi, exp_y_inv)| wRi * exp_y_inv)
            .chain(iter::repeat(Scalar::ZERO).take(pad))
            .collect();

        let delta = inner_product(&yneg_wR[0..n], &wL);

        #[cfg(feature = "parallel")]
        let g_scalars: Vec<Scalar> = s_g_cir
            .par_iter()
            .zip(yneg_wR.par_iter())
            .map(|(s_g_i, yneg_wR_i)| s_g_i - x * yneg_wR_i * s_P_cir)
            .collect();
        #[cfg(not(feature = "parallel"))]
        let g_scalars: Vec<Scalar> = s_g_cir
            .iter()
            .zip(yneg_wR.iter())
            .map(|(s_g_i, yneg_wR_i)| s_g_i - x * yneg_wR_i * s_P_cir)
            .collect();

        let rC: Vec<Scalar> = wV.to_vec();

        #[cfg(feature = "parallel")]
        let h_scalars: Vec<Scalar> = {
            wL.resize(padded_n, Scalar::ZERO);
            wO.resize(padded_n, Scalar::ZERO);
            s_h_cir
                .par_iter()
                .zip(y_inv_vec.par_iter())
                .zip(wL.par_iter())
                .zip(wO.par_iter())
                .zip(rC.par_iter())
                .map(|((((s_h_i, y_inv_i), wLi), wOi), rCi)| {
                    let term1 = y_inv_i * s_h_i;
                    let term2 = (y_inv_i * (x * wLi + wOi) - Scalar::ONE) * (-s_P_cir);
                    let term3 = y_inv_i * x_ipp * (-s_P_cir) * rCi;
                    term1 + term2 + term3
                })
                .collect()
        };
        #[cfg(not(feature = "parallel"))]
        let h_scalars: Vec<Scalar> = s_h_cir
            .iter()
            .zip(y_inv_vec.iter())
            .zip(wL.into_iter().chain(iter::repeat(Scalar::ZERO).take(pad)))
            .zip(wO.into_iter().chain(iter::repeat(Scalar::ZERO).take(pad)))
            .zip(rC.iter())
            .map(|((((s_h_i, y_inv_i), wLi), wOi), rCi)| {
                let term1 = y_inv_i * s_h_i;
                let term2 = (y_inv_i * (x * wLi + wOi) - Scalar::ONE) * (-s_P_cir);
                let term3 = y_inv_i * x_ipp * (-s_P_cir) * rCi;
                term1 + term2 + term3
            })
            .collect();

        // 4. Verification Check Setup
        let chall_batched_ecp = self.transcript.challenge_scalar(b"chall_batched_ecp");

        let (z_s_vec, s_P, s_A_vec) = proof
            .ecp_batched
            .verification_scalars(padded_n, self.transcript)
            .map_err(|_| R1CSError::VerificationError)?;

        let _tp_r = Instant::now();
        let r = self.transcript.challenge_scalar(b"batching_r");
        if _do_print {
            eprintln!(
                "  [Verif-4] Batching scalar r (HMAC challenge): {:>7.3} ms",
                _tp_r.elapsed().as_secs_f64() * 1000.0
            );
        }

        let xx = x * x;
        let rxx = r * xx;
        let xxx = x * xx;
        let r2 = r * r;

        let T_scalars = [r * x, r * xx, rxx * x, rxx * xx, rxx * xxx, rxx * xx * xx];
        let T_points = [proof.T_1, proof.T_2, proof.T_3, proof.T_4, proof.T_5, proof.T_6];

        let expected_ip = proof.t_x + x_ipp * t_cross + x_ipp * x_ipp * proof.tc_x;

        let B_scalar = w_agg * s_Q_cir - w_agg * expected_ip * s_P_cir
            + r * (xx * (wc + delta) - proof.t_x)
            - r2 * proof.tc_x;

        let B_blinding_scalar = x_ipp * proof.ec_blinding * s_P_cir
            + proof.e_blinding * s_P_cir
            - r2 * proof.tc_x_blinding
            - r * proof.t_x_blinding;

        let r3 = r2 * r;
        let r4 = r3 * r;
        let r5 = r4 * r;

        let s_V_checkS          = r4 * (-s_P);
        let s_S_prime_checkS    = r4 * x_prime * (-s_P);
        let s_S1_prime          = r3 * x_prime * (-s_P);
        let s_S2_prime          = r3 * chall_batched_ecp * x_prime * (-s_P);
        let s_B_checkS          = s_P * r3 * proof.r_blinding;
        let s_C0                = r3 * (-s_P);
        let s_C1                = r3 * chall_batched_ecp * (-s_P);
        let s_B_blinding_checkS = s_P * r4 * proof.ec_blinding;
        let s_h_rest            = s_P * r3 * chall_batched_ecp * proof.r_blinding;

        let s_C1_agg = r3 * chall_batched_ecp * s_P * (-proof.alpha_blinding);
        let s_B_eq6  = r5 * (-proof.alpha_blinding);

        let final_scalar_V          = (-x_ipp * s_P_cir) + s_V_checkS;
        let final_scalar_S_prime    = (-x_ipp * s_P_cir * x_prime) + s_S_prime_checkS;
        let final_scalar_B          = B_scalar + s_B_checkS + s_B_eq6;
        let final_scalar_B_blinding = B_blinding_scalar + s_B_blinding_checkS;

        #[cfg(feature = "parallel")]
        let final_g_scalars: Vec<Scalar> = g_scalars
            .par_iter()
            .zip(z_s_vec.par_iter())
            .map(|(g_i, z_i)| g_i + (z_i * r4))
            .collect();
        #[cfg(not(feature = "parallel"))]
        let final_g_scalars: Vec<Scalar> = g_scalars
            .iter()
            .zip(z_s_vec.iter())
            .map(|(g_i, z_i)| g_i + (z_i * r4))
            .collect();

        // 5. Final MSM Construction
        let k_original = C1_prime.len();

        let pi5_scalars = vec![
            r5 * x_prime,
            r5 * (-Scalar::ONE),
        ];

        if _do_print {
            eprintln!("  [Verif-A] Transcript + Scalars: {:>7.1} ms",
                _tp.elapsed().as_secs_f64() * 1000.0);
        }
        let _tp = Instant::now();

        // 6. Final Execution
        #[cfg(feature = "parallel")]
        let mega_check = {
            let ((c1_sc, c2_sc), (c1p_sc, c2p_sc)) = rayon::join(
                || rayon::join(
                    || e_challenge[0..k_original].par_iter().map(|ei| *ei * (s_C0 + s_C1_agg)).collect::<Vec<_>>(),
                    || e_challenge[0..k_original].par_iter().map(|ei| *ei * s_C1).collect::<Vec<_>>(),
                ),
                || rayon::join(
                    || z_s_vec[0..k_original].par_iter().map(|z| z * r3).collect::<Vec<_>>(),
                    || z_s_vec[0..k_original].par_iter().map(|z| z * r3 * chall_batched_ecp).collect::<Vec<_>>(),
                ),
            );
            let cipher_scalars: Vec<Scalar> = c1_sc.into_iter()
                .chain(c2_sc).chain(c1p_sc).chain(c2p_sc)
                .collect();

            let cipher_points: Vec<CompressedRistretto> = c1_raw[0..k_original].iter()
                .chain(c2_raw[0..k_original].iter())
                .chain(C1_prime.iter()).chain(C2_prime.iter())
                .cloned().collect();

            let rest_scalars: Vec<Scalar> = iter::once(-x * s_P_cir)
                .chain(iter::once(-x * x * s_P_cir))
                .chain(iter::once(-x * x * x * s_P_cir))
                .chain(iter::once(final_scalar_V))
                .chain(iter::once(final_scalar_S_prime))
                .chain(iter::once(final_scalar_B))
                .chain(iter::once(final_scalar_B_blinding))
                .chain(iter::once(s_h_rest))
                .chain(final_g_scalars.into_iter())
                .chain(h_scalars.into_iter())
                .chain(s_U_cir.iter().map(|s| -s))
                .chain(iter::once(r2 * x_prime))
                .chain(iter::once(r2))
                .chain(T_scalars.iter().cloned())
                .chain(iter::once(s_S1_prime))
                .chain(iter::once(s_S2_prime))
                .chain(pi5_scalars.into_iter())
                .chain(s_A_vec.iter().map(|s_A| -s_A * r4))
                .chain(s_A_vec.iter().map(|s_A| -s_A * r3))
                .collect();

            let _tp_b = Instant::now();

            let pt_AI  = proof.A_I.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_AO  = proof.A_O.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_S   = proof.S.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_V   = self.V.first()
                .and_then(|v| v.decompress()).ok_or(R1CSError::VerificationError)?;
            let pt_Sp  = proof.S_prime.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_T1p = proof.T_1_prime.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_T2  = proof.T_2.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_T: Vec<RistrettoPoint> = T_points.iter()
                .map(|T| T.decompress().ok_or(R1CSError::VerificationError))
                .collect::<Result<Vec<_>, _>>()?;
            let pt_S1p = proof.S1_prime.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_S2p = proof.S2_prime.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_SK  = proof.S_K.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_alpha = alpha_pub.decompress().ok_or(R1CSError::VerificationError)?;
            let pt_ecp_A0: Vec<RistrettoPoint> = proof.ecp_batched.A_vecs.iter().flatten()
                .map(|A| A[0].decompress().ok_or(R1CSError::VerificationError))
                .collect::<Result<Vec<_>, _>>()?;
            let pt_ecp_A1: Vec<RistrettoPoint> = proof.ecp_batched.A_vecs.iter().flatten()
                .map(|A| A[1].decompress().ok_or(R1CSError::VerificationError))
                .collect::<Result<Vec<_>, _>>()?;

            let rest_points: Vec<RistrettoPoint> = iter::once(pt_AI)
                .chain(iter::once(pt_AO))
                .chain(iter::once(pt_S))
                .chain(iter::once(pt_V))
                .chain(iter::once(pt_Sp))
                .chain(iter::once(self.pc_gens.B))
                .chain(iter::once(self.pc_gens.B_blinding))
                .chain(iter::once(h_rest))   
                .chain(gens.G(padded_n).cloned())
                .chain(gens.H(padded_n).cloned())
                .chain(U_points_decompressed_cir.into_iter())
                .chain(iter::once(pt_T1p))
                .chain(iter::once(pt_T2))
                .chain(pt_T.into_iter())
                .chain(iter::once(pt_S1p))
                .chain(iter::once(pt_S2p))
                .chain(iter::once(pt_SK))
                .chain(iter::once(pt_alpha))
                .chain(pt_ecp_A0.into_iter())
                .chain(pt_ecp_A1.into_iter())
                .collect();

            assert_eq!(
                rest_scalars.len(), rest_points.len(),
                "Scalar/point count mismatch (rest): {} scalars, {} points",
                rest_scalars.len(), rest_points.len()
            );

            if _do_print {
                eprintln!(
                    "  [Verif-B] Point setup (eager decompress {} proof pts): {:>5.1} ms",
                    rest_points.len(),
                    _tp_b.elapsed().as_secs_f64() * 1000.0
                );
            }

            let _tp_c = Instant::now();
            let (cipher_opt, rest_pt) = rayon::join(
                || chunked_optional_multiscalar_mul(&cipher_scalars, &cipher_points),
                || chunked_vartime_multiscalar_mul(&rest_scalars, &rest_points),
            );
            let cipher_result = cipher_opt.ok_or(R1CSError::VerificationError)?;

            if _do_print {
                eprintln!(
                    "  [Verif-C] Split MSM ({} cipher + {} rest pts): {:>5.1} ms  ({} threads)",
                    cipher_points.len(), rest_points.len(),
                    _tp_c.elapsed().as_secs_f64() * 1000.0,
                    rayon::current_num_threads()
                );
                eprintln!(
                    "  [Verif-TOTAL]:                  {:>7.1} ms",
                    _t_total.elapsed().as_secs_f64() * 1000.0
                );
            }

            cipher_result + rest_pt
        };

        #[cfg(not(feature = "parallel"))]
        let mega_check = {
            let combined_scalars: Vec<Scalar> = iter::once(-x * s_P_cir)
                .chain(iter::once(-x * x * s_P_cir))
                .chain(iter::once(-x * x * x * s_P_cir))
                .chain(iter::once(final_scalar_V))
                .chain(iter::once(final_scalar_S_prime))
                .chain(iter::once(final_scalar_B))
                .chain(iter::once(final_scalar_B_blinding))
                .chain(iter::once(s_h_rest))
                .chain(final_g_scalars.into_iter())
                .chain(h_scalars.into_iter())
                .chain(s_U_cir.iter().map(|s| -s))
                .chain(iter::once(r2 * x_prime))
                .chain(iter::once(r2))
                .chain(T_scalars.iter().cloned())
                .chain(iter::once(s_S1_prime))
                .chain(iter::once(s_S2_prime))
                .chain(e_challenge[0..k_original].iter().map(|ei| *ei * (s_C0 + s_C1_agg)))
                .chain(e_challenge[0..k_original].iter().map(|ei| *ei * s_C1))
                .chain(z_s_vec[0..k_original].iter().map(|z| z * r3))
                .chain(z_s_vec[0..k_original].iter().map(|z| z * r3 * chall_batched_ecp))
                .chain(pi5_scalars.into_iter())
                .chain(s_A_vec.iter().map(|s_A| -s_A * r4))
                .chain(s_A_vec.iter().map(|s_A| -s_A * r3))
                .collect();

            let pi5_points: Vec<Option<RistrettoPoint>> = vec![
                proof.S_K.decompress(),
                alpha_pub.decompress(),
            ];

            let ecp_a0: Vec<Option<RistrettoPoint>> = proof.ecp_batched.A_vecs
                .iter().flatten().map(|A| A[0].decompress()).collect();
            let ecp_a1: Vec<Option<RistrettoPoint>> = proof.ecp_batched.A_vecs
                .iter().flatten().map(|A| A[1].decompress()).collect();

            let combined_points_iter = iter::once(proof.A_I.decompress())
                .chain(iter::once(proof.A_O.decompress()))
                .chain(iter::once(proof.S.decompress()))
                .chain(iter::once(self.V.first().and_then(|v| v.decompress())))
                .chain(iter::once(proof.S_prime.decompress()))
                .chain(iter::once(Some(self.pc_gens.B)))
                .chain(iter::once(Some(self.pc_gens.B_blinding)))
                .chain(iter::once(Some(h_rest)))   
                .chain(gens.G(padded_n).cloned().map(Some))
                .chain(gens.H(padded_n).cloned().map(Some))
                .chain(U_points_decompressed_cir.into_iter().map(Some))
                .chain(iter::once(proof.T_1_prime.decompress()))
                .chain(iter::once(proof.T_2.decompress()))
                .chain(T_points.iter().map(|T| T.decompress()))
                .chain(iter::once(proof.S1_prime.decompress()))
                .chain(iter::once(proof.S2_prime.decompress()))
                .chain(c1_raw[0..k_original].iter().map(|p| p.decompress()))
                .chain(c2_raw[0..k_original].iter().map(|p| p.decompress()))
                .chain(C1_prime.iter().map(|c| c.decompress()))
                .chain(C2_prime.iter().map(|c| c.decompress()))
                .chain(pi5_points.into_iter())
                .chain(ecp_a0.into_iter())
                .chain(ecp_a1.into_iter());

            let result = RistrettoPoint::optional_multiscalar_mul(combined_scalars, combined_points_iter)
                .ok_or(R1CSError::VerificationError)?;

            if _do_print {
                eprintln!("  [Verif-TOTAL]:                  {:>7.1} ms",
                    _t_total.elapsed().as_secs_f64() * 1000.0);
            }

            result
        };

        if !mega_check.is_identity() {
            return Err(R1CSError::VerificationError);
        }

        Ok(())
    }
}

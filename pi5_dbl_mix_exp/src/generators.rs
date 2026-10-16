#![allow(unused_variables)]
#![allow(non_snake_case)]
#![deny(missing_docs)]

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_COMPRESSED;
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::VartimeMultiscalarMul;

use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

#[derive(Copy, Clone)]
/// Pedersen commitment generators
pub struct PedersenGens {
    /// ElGamal generator g
    pub B: RistrettoPoint,
    /// Pedersen blinding base h
    pub B_blinding: RistrettoPoint,
    /// ElGamal public key base f_1 (group1)
    pub F: RistrettoPoint,
    /// ElGamal public key base f_2 (group2, dual-group mode)
    pub F2: RistrettoPoint,
}

impl PedersenGens {
    /// Creates a Pedersen commitment using the value scalar and a blinding factor.
    pub fn commit(&self, value: Scalar, blinding: Scalar) -> RistrettoPoint {
        RistrettoPoint::vartime_multiscalar_mul(&[value, blinding], &[self.B, self.B_blinding])
    }
}

impl Default for PedersenGens {
    fn default() -> Self {
        let b0 = RISTRETTO_BASEPOINT_COMPRESSED.as_bytes();

        let derive_generator = |label: &[u8]| -> RistrettoPoint {
            let mut msg1 = Vec::with_capacity(label.len() + 1);
            msg1.extend_from_slice(label);
            msg1.push(0x01);
            let mut msg2 = Vec::with_capacity(label.len() + 1);
            msg2.extend_from_slice(label);
            msg2.push(0x02);

            let mut mac1 = HmacSha256::new_from_slice(b0).unwrap();
            mac1.update(&msg1);
            let eta1: [u8; 32] = mac1.finalize().into_bytes().into();

            let mut mac2 = HmacSha256::new_from_slice(b0).unwrap();
            mac2.update(&msg2);
            let eta2: [u8; 32] = mac2.finalize().into_bytes().into();

            let mut buf = [0u8; 64];
            buf[..32].copy_from_slice(&eta1);
            buf[32..].copy_from_slice(&eta2);
            RistrettoPoint::from_uniform_bytes(&buf)
        };

        let b_blinding = derive_generator(b"PedersenGens_blinding");
        let f          = derive_generator(b"PedersenGens_F");
        let f2         = derive_generator(b"PedersenGens_F2");

        PedersenGens {
            B:          RISTRETTO_BASEPOINT_POINT,
            B_blinding: b_blinding,
            F:          f,
            F2:         f2,
        }
    }
}

///
#[derive(Clone)]
pub struct BulletproofGens {
    /// The maximum number of usable generators for each party.
    pub gens_capacity: usize,
    /// Number of values or parties
    pub party_capacity: usize,
    /// Precomputed \\(\mathbf G\\) generators for each party.
    pub G_vec: Vec<Vec<RistrettoPoint>>,
    /// Precomputed \\(\mathbf H\\) generators for each party.
    pub H_vec: Vec<Vec<RistrettoPoint>>,
    /// HMAC-SHA-256 seed used to derive G generators for party 0.
    pub G_seed: [u8; 32],
    /// HMAC-SHA-256 seed used to derive H generators for party 0.
    pub H_seed: [u8; 32],
}

impl BulletproofGens {
    /// Create a new `BulletproofGens` object.
    ///
    /// # Inputs
    ///
    /// * `gens_capacity` is the number of generators to precompute
    ///    for each party.
    /// * `party_capacity` is the maximum number of parties that can
    ///    produce an aggregated proof.
    pub fn new(gens_capacity: usize, party_capacity: usize) -> Self {
        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;

            let gen_party = |type_byte: u8, party_index: u32| -> ([u8; 32], Vec<RistrettoPoint>) {
                let mut label = [type_byte, 0u8, 0, 0, 0];
                label[1..5].copy_from_slice(&party_index.to_le_bytes());
                let mut mac = HmacSha256::new_from_slice(b"GeneratorsChain").unwrap();
                mac.update(&label);
                let seed: [u8; 32] = mac.finalize().into_bytes().into();

                let base_mac = HmacSha256::new_from_slice(&seed).unwrap();

                let pts: Vec<RistrettoPoint> = (0..gens_capacity)
                    .into_par_iter()
                    .map(|i| {
                        let mut msg = [0u8; 8];
                        msg[0..3].copy_from_slice(b"bp_");
                        msg[3..7].copy_from_slice(&(i as u32).to_le_bytes());
                        msg[7] = 0x01;
                        let mut mac1 = base_mac.clone();
                        mac1.update(&msg);
                        let eta1: [u8; 32] = mac1.finalize().into_bytes().into();
                        msg[7] = 0x02;
                        let mut mac2 = base_mac.clone();
                        mac2.update(&msg);
                        let eta2: [u8; 32] = mac2.finalize().into_bytes().into();
                        let mut buf = [0u8; 64];
                        buf[..32].copy_from_slice(&eta1);
                        buf[32..].copy_from_slice(&eta2);
                        RistrettoPoint::from_uniform_bytes(&buf)
                    })
                    .collect();
                (seed, pts)
            };

            let ((g_seed, g_pts_0), (h_seed, h_pts_0)) = rayon::join(
                || gen_party(b'G', 0),
                || gen_party(b'H', 0),
            );
            let mut g_vec = vec![g_pts_0];
            let mut h_vec = vec![h_pts_0];
            for p in 1..party_capacity as u32 {
                g_vec.push(gen_party(b'G', p).1);
                h_vec.push(gen_party(b'H', p).1);
            }

            return BulletproofGens {
                gens_capacity,
                party_capacity,
                G_vec: g_vec,
                H_vec: h_vec,
                G_seed: g_seed,
                H_seed: h_seed,
            };
        }

        #[cfg(not(feature = "parallel"))]
        {
            let make_seed = |type_byte: u8, party_index: u32| -> [u8; 32] {
                let mut label = [type_byte, 0u8, 0, 0, 0];
                label[1..5].copy_from_slice(&party_index.to_le_bytes());
                let mut mac = HmacSha256::new_from_slice(b"GeneratorsChain").unwrap();
                mac.update(&label);
                mac.finalize().into_bytes().into()
            };

            let make_pts = |seed: &[u8; 32]| -> Vec<RistrettoPoint> {
                let base_mac = HmacSha256::new_from_slice(seed).unwrap();
                (0..gens_capacity)
                    .map(|i| {
                        let mut msg = [0u8; 8];
                        msg[0..3].copy_from_slice(b"bp_");
                        msg[3..7].copy_from_slice(&(i as u32).to_le_bytes());
                        msg[7] = 0x01;
                        let mut mac1 = base_mac.clone();
                        mac1.update(&msg);
                        let eta1: [u8; 32] = mac1.finalize().into_bytes().into();
                        msg[7] = 0x02;
                        let mut mac2 = base_mac.clone();
                        mac2.update(&msg);
                        let eta2: [u8; 32] = mac2.finalize().into_bytes().into();
                        let mut buf = [0u8; 64];
                        buf[..32].copy_from_slice(&eta1);
                        buf[32..].copy_from_slice(&eta2);
                        RistrettoPoint::from_uniform_bytes(&buf)
                    })
                    .collect()
            };

            let g_seed = make_seed(b'G', 0);
            let h_seed = make_seed(b'H', 0);

            BulletproofGens {
                gens_capacity,
                party_capacity,
                G_vec: (0..party_capacity as u32)
                    .map(|p| {
                        let seed = if p == 0 { g_seed } else { make_seed(b'G', p) };
                        make_pts(&seed)
                    })
                    .collect(),
                H_vec: (0..party_capacity as u32)
                    .map(|p| {
                        let seed = if p == 0 { h_seed } else { make_seed(b'H', p) };
                        make_pts(&seed)
                    })
                    .collect(),
                G_seed: g_seed,
                H_seed: h_seed,
            }
        }
    }

    /// Returns j-th share of generators, with an appropriate
    /// slice of vectors G and H for the j-th range proof.
    pub fn share(&self, j: usize) -> BulletproofGensShare<'_> {
        BulletproofGensShare {
            gens: &self,
            share: j,
        }
    }

    /// Return an iterator over the aggregation of the parties' G generators with given size `n`.
    pub(crate) fn G(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.G_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }

    /// Return an iterator over the aggregation of the parties' H generators with given size `n`.
    pub(crate) fn H(&self, n: usize, m: usize) -> impl Iterator<Item = &RistrettoPoint> {
        AggregatedGensIter {
            n,
            m,
            array: &self.H_vec,
            party_idx: 0,
            gen_idx: 0,
        }
    }
}

struct AggregatedGensIter<'a> {
    array: &'a Vec<Vec<RistrettoPoint>>,
    n: usize,
    m: usize,
    party_idx: usize,
    gen_idx: usize,
}

impl<'a> Iterator for AggregatedGensIter<'a> {
    type Item = &'a RistrettoPoint;

    fn next(&mut self) -> Option<Self::Item> {
        if self.gen_idx >= self.n {
            self.gen_idx = 0;
            self.party_idx += 1;
        }

        if self.party_idx >= self.m {
            None
        } else {
            let cur_gen = self.gen_idx;
            self.gen_idx += 1;
            Some(&self.array[self.party_idx][cur_gen])
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.n * self.m;
        (size, Some(size))
    }
}

/// Represents a view of the generators used by a specific party in an
/// aggregated proof.
///
/// The `BulletproofGens` struct represents generators for an aggregated
/// range proof `m` proofs of `n` bits each; the `BulletproofGensShare`
/// provides a view of the generators for one of the `m` parties' shares.
///
/// The `BulletproofGensShare` is produced by [`BulletproofGens::share()`].
#[derive(Copy, Clone)]
pub struct BulletproofGensShare<'a> {
    /// The parent object that this is a view into
    gens: &'a BulletproofGens,
    /// Which share we are
    share: usize,
}

impl<'a> BulletproofGensShare<'a> {
    /// Return an iterator over this party's G generators with given size `n`.
    pub(crate) fn G(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.G_vec[self.share].iter().take(n)
    }

    /// Return an iterator over this party's H generators with given size `n`.
    pub(crate) fn H(&self, n: usize) -> impl Iterator<Item = &'a RistrettoPoint> {
        self.gens.H_vec[self.share].iter().take(n)
    }
}

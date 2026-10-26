//! Definition of the proof struct.

use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;

use inner_product_proof::prove_ecp;
use inner_product_proof::prove_ipa;

use errors::ProofError;
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize, Serializer};
use std::convert::TryInto;

/// A proof of some statement specified by a
/// [`ConstraintSystem`](::r1cs::ConstraintSystem).
#[derive(Clone, Debug)]
#[allow(non_snake_case)]
pub struct R1CSProof {
    /// Commitment to the values of input wires
    pub(super) A_I: CompressedRistretto,
    /// Commitment to the values of output wires
    pub(super) A_O: CompressedRistretto,
    /// Commitment to the blinding factors
    pub(super) S: CompressedRistretto,

    /// Commitment to the \\(t_1\\) coefficient of \\( t(x) \\)
    pub(super) T_1: CompressedRistretto,
    /// Commitment to the \\(t_2\\) coefficient
    pub(super) T_2: CompressedRistretto,
    /// Commitment to the \\(t_3\\) coefficient of \\( t(x) \\)
    pub(super) T_3: CompressedRistretto,
    /// Commitment to the \\(t_4\\) coefficient of \\( t(x) \\)
    pub(super) T_4: CompressedRistretto,
    /// Commitment to the \\(t_5\\) coefficient of \\( t(x) \\)
    pub(super) T_5: CompressedRistretto,
    /// Commitment to the \\(t_6\\) coefficient of \\( t(x) \\)
    pub(super) T_6: CompressedRistretto,

    /// Evaluation of the polynomial \\(t(x)\\) at the challenge point \\(x\\)
    pub(super) t_x: Scalar,
    /// Blinding factor for the synthetic commitment to \\( t(x) \\)
    pub(super) t_x_blinding: Scalar,
    /// Blinding factor for the synthetic commitment to the inner-product arguments
    pub(super) e_blinding: Scalar,

    /// Batched IPA proof
    pub(super) ipp_proof: prove_ipa,

    /// Shuffle consistency commitments
    pub(super) S_prime: CompressedRistretto,
    pub(super) T_1_prime: CompressedRistretto,

    /// Consistency check scalars
    pub(super) tc_x: Scalar,
    pub(super) tc_x_blinding: Scalar,
    pub(super) ec_blinding: Scalar,
    pub(super) t_cross: Scalar,

    pub(super) S_primes: Vec<CompressedRistretto>,
    pub(super) r_blindings: Vec<Scalar>,

    /// Batched eCP proof
    pub(super) ecp_batched: prove_ecp,
}

impl R1CSProof {
    /// Serializes the proof into a byte array.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();

        buf.extend_from_slice(self.A_I.as_bytes());
        buf.extend_from_slice(self.A_O.as_bytes());
        buf.extend_from_slice(self.S.as_bytes());
        buf.extend_from_slice(self.T_1.as_bytes());
        buf.extend_from_slice(self.T_2.as_bytes());
        buf.extend_from_slice(self.T_3.as_bytes());
        buf.extend_from_slice(self.T_4.as_bytes());
        buf.extend_from_slice(self.T_5.as_bytes());
        buf.extend_from_slice(self.T_6.as_bytes());
        buf.extend_from_slice(self.S_prime.as_bytes());
        buf.extend_from_slice(self.T_1_prime.as_bytes());

        buf.extend_from_slice(self.t_x.as_bytes());
        buf.extend_from_slice(self.t_x_blinding.as_bytes());
        buf.extend_from_slice(self.e_blinding.as_bytes());
        buf.extend_from_slice(self.tc_x.as_bytes());
        buf.extend_from_slice(self.tc_x_blinding.as_bytes());
        buf.extend_from_slice(self.ec_blinding.as_bytes());
        buf.extend_from_slice(self.t_cross.as_bytes());

        // Variable: per-group commitments (length-prefixed)
        buf.extend_from_slice(&(self.S_primes.len() as u64).to_le_bytes());
        for pt in &self.S_primes {
            buf.extend_from_slice(pt.as_bytes());
        }

        // Variable: per-group rerandomization responses (length-prefixed)
        buf.extend_from_slice(&(self.r_blindings.len() as u64).to_le_bytes());
        for sc in &self.r_blindings {
            buf.extend_from_slice(sc.as_bytes());
        }

        let ipp_proof_bytes = self.ipp_proof.to_bytes();
        let ecp_batched_bytes = self.ecp_batched.to_bytes();

        buf.extend_from_slice(&(ipp_proof_bytes.len() as u64).to_le_bytes());
        buf.extend_from_slice(&(ecp_batched_bytes.len() as u64).to_le_bytes());

        buf.extend_from_slice(ipp_proof_bytes.as_slice());
        buf.extend_from_slice(ecp_batched_bytes.as_slice());

        buf
    }

    /// Deserializes the proof from a byte slice.
    pub fn from_bytes(slice: &[u8]) -> Result<R1CSProof, ProofError> {
        let fixed_len = (11 + 7) * 32;
        let min_len = fixed_len + 8 + 8 + 8 + 8; 
        if slice.len() < min_len {
            return Err(ProofError::FormatError);
        }

        let mut offset = 0;
        use util::read32;

        macro_rules! read_point {
            () => {{
                if offset + 32 > slice.len() {
                    return Err(ProofError::FormatError);
                }
                let pt = CompressedRistretto(read32(&slice[offset..]));
                offset += 32;
                pt
            }};
        }

        macro_rules! read_scalar {
            () => {{
                if offset + 32 > slice.len() {
                    return Err(ProofError::FormatError);
                }
                let sc = Option::from(Scalar::from_canonical_bytes(read32(&slice[offset..])))
                    .ok_or(ProofError::FormatError)?;
                offset += 32;
                sc
            }};
        }

        macro_rules! read_u64 {
            () => {{
                if offset + 8 > slice.len() {
                    return Err(ProofError::FormatError);
                }
                let bytes: [u8; 8] = slice[offset..offset + 8]
                    .try_into()
                    .map_err(|_| ProofError::FormatError)?;
                offset += 8;
                u64::from_le_bytes(bytes) as usize
            }};
        }

        let A_I = read_point!();
        let A_O = read_point!();
        let S = read_point!();
        let T_1 = read_point!();
        let T_2 = read_point!();
        let T_3 = read_point!();
        let T_4 = read_point!();
        let T_5 = read_point!();
        let T_6 = read_point!();
        let S_prime = read_point!();
        let T_1_prime = read_point!();

        let t_x = read_scalar!();
        let t_x_blinding = read_scalar!();
        let e_blinding = read_scalar!();
        let tc_x = read_scalar!();
        let tc_x_blinding = read_scalar!();
        let ec_blinding = read_scalar!();
        let t_cross = read_scalar!();

        let n_s_primes = read_u64!();
        if n_s_primes
            .checked_mul(32)
            .and_then(|b| b.checked_add(offset))
            .map_or(true, |end| end > slice.len())
        {
            return Err(ProofError::FormatError);
        }
        let mut S_primes = Vec::with_capacity(n_s_primes);
        for _ in 0..n_s_primes {
            S_primes.push(read_point!());
        }

        let n_r_blindings = read_u64!();
        if n_r_blindings
            .checked_mul(32)
            .and_then(|b| b.checked_add(offset))
            .map_or(true, |end| end > slice.len())
        {
            return Err(ProofError::FormatError);
        }
        let mut r_blindings = Vec::with_capacity(n_r_blindings);
        for _ in 0..n_r_blindings {
            r_blindings.push(read_scalar!());
        }

        let ipp_proof_len = read_u64!();
        let ecp_batched_len = read_u64!();

        let total_expected_len = offset
            .checked_add(ipp_proof_len)
            .and_then(|l| l.checked_add(ecp_batched_len))
            .ok_or(ProofError::FormatError)?;
        if slice.len() != total_expected_len {
            return Err(ProofError::FormatError);
        }

        let ipp_proof = prove_ipa::from_bytes(&slice[offset..offset + ipp_proof_len])?;
        offset += ipp_proof_len;

        let ecp_batched = prove_ecp::from_bytes(&slice[offset..offset + ecp_batched_len])?;

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
            S_primes,
            r_blindings,
            ecp_batched,
        })
    }
}

impl Serialize for R1CSProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(&self.to_bytes()[..])
    }
}

impl<'de> Deserialize<'de> for R1CSProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct R1CSProofVisitor;

        impl<'de> Visitor<'de> for R1CSProofVisitor {
            type Value = R1CSProof;

            fn expecting(&self, formatter: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                formatter.write_str("a valid R1CSProof")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<R1CSProof, E>
            where
                E: serde::de::Error,
            {
                R1CSProof::from_bytes(v).map_err(serde::de::Error::custom)
            }
        }

        deserializer.deserialize_bytes(R1CSProofVisitor)
    }
}

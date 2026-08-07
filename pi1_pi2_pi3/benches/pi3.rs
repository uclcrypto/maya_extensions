#![allow(dead_code)]
extern crate maya_ristretto;
use maya_ristretto::r1cs::LinearCombination;
use maya_ristretto::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Variable, Verifier};
use maya_ristretto::transcript::TranscriptProtocol;
use maya_ristretto::{BulletproofGens, PedersenGens};

#[macro_use]
extern crate criterion;
use criterion::Criterion;

extern crate curve25519_dalek;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoBasepointTable, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

use maya_ristretto::HmacTranscript;
type Transcript = HmacTranscript;

extern crate rand;
use rand::seq::SliceRandom;

extern crate hmac;
extern crate sha2;

extern crate bincode;

use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};
use std::time::Instant;

#[cfg(feature = "parallel")]
extern crate rayon;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

const SAMPLES: usize = 10;
const CRITERION_ENABLED: bool = true;

struct KShuffleGadget;

impl KShuffleGadget {
    fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: &[Variable],
        y: &[Scalar],
        k_original: usize,
        block_sizes: &[usize],
    ) {
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len();
        assert_eq!(x.len(), y.len());
        assert_eq!(block_sizes.iter().sum::<usize>(), k_original);

        let v = cs.challenge_scalar(b"block-batch challenge v");
        let mut batched_rhs = Scalar::ZERO;
        let mut v_power = Scalar::ONE;
        let mut batched_lhs = LinearCombination::from(Scalar::ZERO);
        let mut offset = 0;

        for &bs in block_sizes {
            let start = offset;
            let end = offset + bs;
            offset = end;

            let mut prod_y = Scalar::ONE;
            for i in start..end { prod_y *= y[i] - z; }
            batched_rhs += v_power * prod_y;

            let mut prev_lc: LinearCombination = x[start] - z;
            for i in (start + 1)..end {
                let (_, _, out_var) = cs.multiply(prev_lc, x[i] - z);
                prev_lc = LinearCombination::from(out_var);
            }
            batched_lhs = batched_lhs + prev_lc * v_power;
            v_power *= v;
        }

        for i in k_original..k { cs.constrain(x[i] - Scalar::ZERO); }
        cs.constrain(batched_lhs - batched_rhs);
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut HmacTranscript,
        input: &[Scalar],
        output: &[Scalar],
        c1_prime: &[RistrettoPoint],
        c2_prime: &[RistrettoPoint],
        f_gens: &[RistrettoPoint],
        r_primes: &[Scalar],
        k_fold: usize,
        num_rounds: usize,
        p1_blocks: &[usize],    
        p2_groups: &[usize],   
        rng: &mut (impl rand::RngCore + rand::CryptoRng),
    ) -> Result<(R1CSProof, CompressedRistretto), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 { return Err(R1CSError::InputLengthError); }

        transcript.append_message(b"dom-sep", b"ShuffleProof-multikey");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());
        transcript.append_message(b"num_p1_blocks", Scalar::from(p1_blocks.len() as u64).as_bytes());
        for &bs in p1_blocks {
            transcript.append_message(b"p1_block_size", Scalar::from(bs as u64).as_bytes());
        }
        transcript.append_message(b"num_p2_groups", Scalar::from(p2_groups.len() as u64).as_bytes());
        for &gs in p2_groups {
            transcript.append_message(b"p2_group_size", Scalar::from(gs as u64).as_bytes());
        }

        let mut prover = Prover::new(bp_gens, pc_gens, transcript);
        let v_blinding = Scalar::random(rng);
        let (output_commitment, output_vars) = prover.commit_vec(output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, p1_blocks);
        let proof = cs.prove(c1_prime, c2_prime, f_gens, r_primes, p2_groups, k_fold, num_rounds)?;
        Ok((proof, output_commitment))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut HmacTranscript,
        proof: &R1CSProof,
        input: &[Scalar],
        output_commitment: CompressedRistretto,
        c1_prime: &[CompressedRistretto],
        c2_prime: &[CompressedRistretto],
        c1_raw: &[CompressedRistretto],
        c2_raw: &[CompressedRistretto],
        e_challenge: &[Scalar],
        f_gens: &[CompressedRistretto],
        p1_blocks: &[usize],   
        p2_groups: &[usize],  
    ) -> Result<(), R1CSError> {
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof-multikey");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());
        transcript.append_message(b"num_p1_blocks", Scalar::from(p1_blocks.len() as u64).as_bytes());
        for &bs in p1_blocks {
            transcript.append_message(b"p1_block_size", Scalar::from(bs as u64).as_bytes());
        }
        transcript.append_message(b"num_p2_groups", Scalar::from(p2_groups.len() as u64).as_bytes());
        for &gs in p2_groups {
            transcript.append_message(b"p2_group_size", Scalar::from(gs as u64).as_bytes());
        }

        let mut verifier = Verifier::new(bp_gens, pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        let k_original = c1_prime.len();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, p1_blocks);
        cs.verify(proof, c1_prime, c2_prime, c1_raw, c2_raw, e_challenge, f_gens, p2_groups)
    }
}

fn derive_challenge_e(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    c1p_bytes: &[u8],
    c2p_bytes: &[u8],
    f_gens: &[RistrettoPoint],   
    p1_blocks: &[usize],
    p2_groups: &[usize],
    n_original: usize,
    n_padded: usize,
) -> Vec<Scalar> {
    let mut ts = Transcript::new(b"FiatShamir-e-multikey");
    ts.append_message(b"dom-sep", b"challenge-e-derivation");
    ts.commit_point(b"pk_g", &pc_gens.B.compress());
    ts.commit_point(b"ck_h", &pc_gens.B_blinding.compress());
    <Transcript as TranscriptProtocol>::commit_u64(&mut ts, b"ck_n", bp_gens.gens_capacity as u64);
    ts.append_message(b"ck_g_seed", &bp_gens.G_seed);
    ts.append_message(b"ck_h_seed", &bp_gens.H_seed);
    for f in f_gens { ts.commit_point(b"pk_f_ell", &f.compress()); }
    ts.append_message(b"c1",  c1_bytes);
    ts.append_message(b"c2",  c2_bytes);
    ts.append_message(b"c1p", c1p_bytes);
    ts.append_message(b"c2p", c2p_bytes);
    ts.append_message(b"num_p1_blocks", &(p1_blocks.len() as u64).to_le_bytes());
    for &bs in p1_blocks { ts.append_message(b"p1_block_size", &(bs as u64).to_le_bytes()); }
    ts.append_message(b"num_p2_groups", &(p2_groups.len() as u64).to_le_bytes());
    for &gs in p2_groups { ts.append_message(b"p2_group_size", &(gs as u64).to_le_bytes()); }

    let mut seed = [0u8; 32];
    ts.challenge_bytes(b"e_seed", &mut seed);

    use hmac::{Hmac, Mac};
    use sha2::Sha256;
    type HmacSha256 = Hmac<Sha256>;

    let base_mac = HmacSha256::new_from_slice(&seed).expect("HMAC key");

    #[cfg(feature = "parallel")]
    let mut e: Vec<Scalar> = (0u32..n_original as u32)
        .into_par_iter()
        .map(|i| {
            let i_bytes = i.to_le_bytes();
            let mut info1 = [0u8; 7];
            info1[..2].copy_from_slice(b"e_");
            info1[2..6].copy_from_slice(&i_bytes);
            info1[6] = 0x01;
            let mut info2 = [0u8; 7];
            info2[..2].copy_from_slice(b"e_");
            info2[2..6].copy_from_slice(&i_bytes);
            info2[6] = 0x02;
            let h1: [u8; 32] = {
                let mut m = base_mac.clone();
                m.update(&info1);
                m.finalize().into_bytes().into()
            };
            let h2: [u8; 32] = {
                let mut m = base_mac.clone();
                m.update(&info2);
                m.finalize().into_bytes().into()
            };
            let mut wide = [0u8; 64];
            wide[..32].copy_from_slice(&h1);
            wide[32..].copy_from_slice(&h2);
            Scalar::from_bytes_mod_order_wide(&wide)
        })
        .collect();

    #[cfg(not(feature = "parallel"))]
    let mut e: Vec<Scalar> = {
        let mut v = Vec::with_capacity(n_original);
        for i in 0u32..n_original as u32 {
            let i_bytes = i.to_le_bytes();
            let mut info1 = [0u8; 7];
            info1[..2].copy_from_slice(b"e_");
            info1[2..6].copy_from_slice(&i_bytes);
            info1[6] = 0x01;
            let mut info2 = [0u8; 7];
            info2[..2].copy_from_slice(b"e_");
            info2[2..6].copy_from_slice(&i_bytes);
            info2[6] = 0x02;
            let h1: [u8; 32] = {
                let mut m = base_mac.clone();
                m.update(&info1);
                m.finalize().into_bytes().into()
            };
            let h2: [u8; 32] = {
                let mut m = base_mac.clone();
                m.update(&info2);
                m.finalize().into_bytes().into()
            };
            let mut wide = [0u8; 64];
            wide[..32].copy_from_slice(&h1);
            wide[32..].copy_from_slice(&h2);
            v.push(Scalar::from_bytes_mod_order_wide(&wide));
        }
        v
    };

    e.resize(n_padded, Scalar::ZERO);
    e
}

fn batch_compress(points: &[RistrettoPoint]) -> Vec<u8> {
    let mut blob = vec![0u8; points.len() * 32];
    #[cfg(not(feature = "parallel"))]
    for (chunk, pt) in blob.chunks_exact_mut(32).zip(points.iter()) {
        chunk.copy_from_slice(pt.compress().as_bytes());
    }
    #[cfg(feature = "parallel")]
    blob.par_chunks_exact_mut(32)
        .zip(points.par_iter())
        .for_each(|(chunk, pt)| chunk.copy_from_slice(pt.compress().as_bytes()));
    blob
}


fn blob_to_compressed(blob: &[u8]) -> Vec<CompressedRistretto> {
    assert_eq!(blob.len() % 32, 0, "blob length must be a multiple of 32");
    blob.chunks_exact(32)
        .map(|c| {
            let mut arr = [0u8; 32];
            arr.copy_from_slice(c);
            CompressedRistretto(arr)
        })
        .collect()
}


fn compress_all_par(points: &[RistrettoPoint]) -> Vec<CompressedRistretto> {
    #[cfg(feature = "parallel")]
    {
        points.par_iter().map(|p| p.compress()).collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        points.iter().map(|p| p.compress()).collect()
    }
}

fn batch_decompress(blob: &[u8]) -> std::io::Result<Vec<RistrettoPoint>> {
    assert_eq!(blob.len() % 32, 0, "blob length must be a multiple of 32 bytes");
    #[cfg(feature = "parallel")]
    {
        blob.par_chunks(32)
            .map(|chunk| {
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
                    .decompress()
                    .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed"))
            })
            .collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        let mut out = Vec::with_capacity(blob.len() / 32);
        for chunk in blob.chunks(32) {
            out.push(
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
                    .decompress()
                    .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed"))?,
            );
        }
        Ok(out)
    }
}

fn write_ciphertexts_mk(
    path: &str,
    c1: &[RistrettoPoint],
    c2: &[RistrettoPoint],
    g: &RistrettoPoint,
    h: &RistrettoPoint,
    f_gens: &[RistrettoPoint],
) -> std::io::Result<usize> {
    let n = c1.len();
    assert_eq!(n, c2.len());
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(n as u64).to_le_bytes())?;
    #[cfg(feature = "parallel")]
    {
        let (c1_blob, c2_blob) = rayon::join(|| batch_compress(c1), || batch_compress(c2));
        w.write_all(&c1_blob)?;
        w.write_all(&c2_blob)?;
    }
    #[cfg(not(feature = "parallel"))]
    for pt in c1.iter().chain(c2.iter()) {
        w.write_all(pt.compress().as_bytes())?;
    }
    w.write_all(g.compress().as_bytes())?;
    w.write_all(h.compress().as_bytes())?;
    w.write_all(&(f_gens.len() as u64).to_le_bytes())?;
    for f in f_gens { w.write_all(f.compress().as_bytes())?; }
    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_ciphertexts_mk(path: &str) -> std::io::Result<(
    Vec<RistrettoPoint>, Vec<RistrettoPoint>,
    RistrettoPoint, RistrettoPoint,
    Vec<RistrettoPoint>,
    Vec<u8>, Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    let mut buf32 = [0u8; 32];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

    let decomp_pt = |b: [u8; 32], label: &'static str| -> std::io::Result<RistrettoPoint> {
        CompressedRistretto::from_slice(&b)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
            .decompress()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("decompress {} failed", label)))
    };

    #[cfg(feature = "parallel")]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut blob = vec![0u8; 2 * n * 32];
        r.read_exact(&mut blob)?;
        let s = n * 32;
        let c1_raw = blob[..s].to_vec();
        let c2_raw = blob[s..].to_vec();
        let (r1, r2) = rayon::join(|| batch_decompress(&c1_raw), || batch_decompress(&c2_raw));
        (r1?, r2?, c1_raw, c2_raw)
    };
    #[cfg(not(feature = "parallel"))]
    let (c1, c2, c1_raw, c2_raw) = {
        let mut pts1 = Vec::with_capacity(n);
        let mut raw1 = Vec::with_capacity(n * 32);
        for _ in 0..n {
            r.read_exact(&mut buf32)?;
            raw1.extend_from_slice(&buf32);
            pts1.push(decomp_pt(buf32, "c1")?);
        }
        let mut pts2 = Vec::with_capacity(n);
        let mut raw2 = Vec::with_capacity(n * 32);
        for _ in 0..n {
            r.read_exact(&mut buf32)?;
            raw2.extend_from_slice(&buf32);
            pts2.push(decomp_pt(buf32, "c2")?);
        }
        (pts1, pts2, raw1, raw2)
    };
    r.read_exact(&mut buf32)?; let g = decomp_pt(buf32, "g")?;
    r.read_exact(&mut buf32)?; let h = decomp_pt(buf32, "h")?;

    r.read_exact(&mut buf8)?;
    let num_f = u64::from_le_bytes(buf8) as usize;
    let mut f_gens_out = Vec::with_capacity(num_f);
    for _ in 0..num_f {
        r.read_exact(&mut buf32)?;
        f_gens_out.push(decomp_pt(buf32, "f_gen")?);
    }

    Ok((c1, c2, g, h, f_gens_out, c1_raw, c2_raw))
}

fn write_proof_bundle(
    path: &str,
    proof: &R1CSProof,
    out_commitment: &CompressedRistretto,
    c1p_blob: &[u8],
    c2p_blob: &[u8],
) -> std::io::Result<usize> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    let proof_bytes = proof.to_bytes();
    w.write_all(&(proof_bytes.len() as u64).to_le_bytes())?;
    w.write_all(&proof_bytes)?;
    w.write_all(out_commitment.as_bytes())?;
    for blob in &[c1p_blob, c2p_blob] {
        w.write_all(&((blob.len() / 32) as u64).to_le_bytes())?;
        w.write_all(blob)?;
    }
    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}

fn read_proof_bundle(path: &str) -> std::io::Result<(
    R1CSProof, CompressedRistretto,
    Vec<RistrettoPoint>, Vec<RistrettoPoint>,
    Vec<u8>, Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    let mut buf32 = [0u8; 32];

    r.read_exact(&mut buf8)?;
    let proof_len = u64::from_le_bytes(buf8) as usize;
    let mut proof_bytes = vec![0u8; proof_len];
    r.read_exact(&mut proof_bytes)?;
    let proof: R1CSProof = R1CSProof::from_bytes(&proof_bytes).expect("proof deserialize");

    r.read_exact(&mut buf32)?;
    let out_commitment = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?;

    let read_blob = |rdr: &mut BufReader<File>| -> std::io::Result<Vec<u8>> {
        let mut b8 = [0u8; 8];
        rdr.read_exact(&mut b8)?;
        let cnt = u64::from_le_bytes(b8) as usize;
        let mut blob = vec![0u8; cnt * 32];
        rdr.read_exact(&mut blob)?;
        Ok(blob)
    };
    let c1p_blob = read_blob(&mut r)?;
    let c2p_blob = read_blob(&mut r)?;
    #[cfg(feature = "parallel")]
    let (c1_prime, c2_prime) = {
        let (r1, r2) = rayon::join(|| batch_decompress(&c1p_blob), || batch_decompress(&c2p_blob));
        (r1?, r2?)
    };
    #[cfg(not(feature = "parallel"))]
    let c1_prime = batch_decompress(&c1p_blob)?;
    #[cfg(not(feature = "parallel"))]
    let c2_prime = batch_decompress(&c2p_blob)?;
    Ok((proof, out_commitment, c1_prime, c2_prime, c1p_blob, c2p_blob))
}


fn read_ciphertexts_mk_raw(path: &str) -> std::io::Result<(
    Vec<u8>, Vec<u8>,
    RistrettoPoint, RistrettoPoint,
    Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    let mut buf32 = [0u8; 32];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

    let mut blob = vec![0u8; 2 * n * 32];
    r.read_exact(&mut blob)?;
    let s = n * 32;
    let c1_raw = blob[..s].to_vec();
    let c2_raw = blob[s..].to_vec();

    let decomp_pt = |b: [u8; 32], label: &'static str| -> std::io::Result<RistrettoPoint> {
        CompressedRistretto::from_slice(&b)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
            .decompress()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("decompress {} failed", label)))
    };
    r.read_exact(&mut buf32)?; let g = decomp_pt(buf32, "g")?;
    r.read_exact(&mut buf32)?; let h = decomp_pt(buf32, "h")?;

    r.read_exact(&mut buf8)?;
    let num_f = u64::from_le_bytes(buf8) as usize;
    let mut f_gens_blob = vec![0u8; num_f * 32];
    r.read_exact(&mut f_gens_blob)?;

    Ok((c1_raw, c2_raw, g, h, f_gens_blob))
}

fn read_proof_bundle_raw(path: &str) -> std::io::Result<(
    R1CSProof, CompressedRistretto, Vec<u8>, Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    let mut buf32 = [0u8; 32];

    r.read_exact(&mut buf8)?;
    let proof_len = u64::from_le_bytes(buf8) as usize;
    let mut proof_bytes = vec![0u8; proof_len];
    r.read_exact(&mut proof_bytes)?;
    let proof: R1CSProof = R1CSProof::from_bytes(&proof_bytes).expect("proof deserialize");

    r.read_exact(&mut buf32)?;
    let out_commitment = CompressedRistretto::from_slice(&buf32)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?;

    let read_blob = |rdr: &mut BufReader<File>| -> std::io::Result<Vec<u8>> {
        let mut b8 = [0u8; 8];
        rdr.read_exact(&mut b8)?;
        let cnt = u64::from_le_bytes(b8) as usize;
        let mut blob = vec![0u8; cnt * 32];
        rdr.read_exact(&mut blob)?;
        Ok(blob)
    };
    let c1p_blob = read_blob(&mut r)?;
    let c2p_blob = read_blob(&mut r)?;

    Ok((proof, out_commitment, c1p_blob, c2p_blob))
}

fn generate_hetero_block_permutation(block_sizes: &[usize], rng: &mut impl rand::RngCore) -> Vec<usize> {
    let n: usize = block_sizes.iter().sum();
    let mut indices: Vec<usize> = (0..n).collect();
    let mut offset = 0;
    for &bs in block_sizes {
        indices[offset..offset + bs].shuffle(rng);
        offset += bs;
    }
    indices
}

struct CityConfig {
    voters: usize,                        
    candidates_per_question: Vec<usize>,  
}

impl CityConfig {
    fn questions(&self) -> usize { self.candidates_per_question.len() }
    fn total_ciphertexts(&self) -> usize {
        self.voters * self.candidates_per_question.iter().sum::<usize>()
    }
    fn b_desc(&self) -> String {
        if self.candidates_per_question.windows(2).all(|w| w[0] == w[1]) {
            format!("b={}", self.candidates_per_question[0])
        } else {
            format!("b=[{}]", self.candidates_per_question.iter()
                .map(|b| b.to_string()).collect::<Vec<_>>().join(","))
        }
    }
    fn b_label(&self) -> String {
        if self.candidates_per_question.windows(2).all(|w| w[0] == w[1]) {
            format!("b{}", self.candidates_per_question[0])
        } else {
            format!("b{}", self.candidates_per_question.iter()
                .map(|b| b.to_string()).collect::<Vec<_>>().join("-"))
        }
    }
}
// Benchmark-only deterministic RNG.
// Replace with OsRng or another OS-seeded CSPRNG outside tests/benchmarks.
#[cfg(all(feature = "parallel", not(feature = "production")))]
fn deterministic_rand_scalar(index: usize) -> Scalar {
    use rand::SeedableRng;
    const DOMAIN_TAG: u64 = 0xD0_53_BE_4C_1A_27_0E_F1;
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    seed[8..16].copy_from_slice(&DOMAIN_TAG.to_le_bytes());
    let mut rng = rand::rngs::StdRng::from_seed(seed);
    Scalar::random(&mut rng)
}

#[allow(unused_variables)]
fn custom_benchmark(c: &mut Criterion) {
    let quick_mode = std::env::var("QUICK")
        .ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();

    let configs: Vec<(usize, Vec<CityConfig>)> = if quick_mode {
        // 2 cities * 50 voters * 1 question * 10 candidates = N=1000, L=2
        vec![(4, vec![
            CityConfig { voters: 50, candidates_per_question: vec![10] },
            CityConfig { voters: 50, candidates_per_question: vec![10] },
        ])]
    } else {
        vec![
            (4, vec![
                CityConfig { voters: 1000, candidates_per_question: vec![37, 63] },
                CityConfig { voters: 500, candidates_per_question: vec![149,14,37] },
            ]),

             (4, vec![
                CityConfig { voters: 10000, candidates_per_question: vec![5] },
                CityConfig { voters: 3500, candidates_per_question: vec![3,7,10] },
                CityConfig { voters: 20000, candidates_per_question: vec![2,2] },

            ]),
            (4, (0..100).map(|_| CityConfig { 
                voters: 1000, 
                candidates_per_question: vec![2] 
                }).collect()),
        ]
    };

    let features = if cfg!(feature = "parallel") { "parallel" } else { "none" };
    println!();
    println!("================================================================");
    println!("  Pi_3 benchmark: multi-key, per-key permutations");
    println!("  Configurations ({} total):", configs.len());
    for (idx, (_k, cities)) in configs.iter().enumerate() {
        let n: usize = cities.iter().map(|c| c.total_ciphertexts()).sum();
        println!("    {:>2}.  N={}  L={}", idx+1, n, cities.len());
        for (ell, city) in cities.iter().enumerate() {
            println!("          Key {}: B={}  x={}  {}  => n={}",
                ell+1, city.voters, city.questions(), city.b_desc(), city.total_ciphertexts());
        }
    }
    println!("  Features: {}", features);
    println!("================================================================");

    let input_ciph_path    = "./maya_ristretto_pi3_input_ciph.bin";
    let output_bundle_path = "./maya_ristretto_pi3_output_bundle.bin";

    #[allow(dead_code)]
    struct RunResult {
        n: usize, k: usize, d: usize, l: usize,
        total_prover_ms: f64, total_verifier_ms: f64,
        proof_bytes: usize, proof_gen_ms: f64, verify_ms: f64,
        label_p: String, label_v: String,
    }
    let mut results: Vec<RunResult> = Vec::new();

    for (i, (k, cities)) in configs.iter().enumerate() {
        let k = *k;
        let l_cities = cities.len();

        let p1_blocks: Vec<usize> = cities.iter()
            .flat_map(|c| {
                std::iter::repeat(c.candidates_per_question.as_slice())
                    .take(c.voters)
                    .flat_map(|cpq| cpq.iter().copied())
                    .collect::<Vec<_>>()
            })
            .collect();
        let p2_groups: Vec<usize> = cities.iter()
            .map(|c| c.total_ciphertexts())
            .collect();
        let n_input: usize = p2_groups.iter().sum();
        let n_padded = n_input + (k - 1) + 1;

        let pc_gens = PedersenGens::default();

        let mut rng = rand::thread_rng();
        let g = pc_gens.B; 
        let f_gens: Vec<RistrettoPoint> = (0..l_cities)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        let t_table_start = Instant::now();
        let f_tables: Vec<RistrettoBasepointTable> = f_gens.iter()
            .map(|f| RistrettoBasepointTable::create(f))
            .collect();

        let g_table = RistrettoBasepointTable::create(&g);
        let t_table = t_table_start.elapsed();

        let rem = n_input % k;
        let circuit_n = if rem == 0 { n_input } else { n_input + (k - rem) };
        let mut n_j = circuit_n;
        let mut d = 0usize;
        while n_j > 1 {
            let r = n_j % k;
            n_j = (n_j + if r == 0 { 0 } else { k - r }) / k;
            d += 1;
        }

        let c1_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
        let c2_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();

        let _file_size = write_ciphertexts_mk(
            input_ciph_path, &c1_raw, &c2_raw, &g, &pc_gens.B_blinding, &f_gens,
        ).expect("write_ciphertexts_mk failed");

        // SINGLE-RUN PROVER

        let t_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let (bp_gens, (c1_bytes, c2_bytes, _g_rd, _h_rd, f_gens_blob)) = rayon::join(
            || BulletproofGens::new(n_padded, 1),
            || read_ciphertexts_mk_raw(input_ciph_path).expect("read_ciphertexts_mk_raw failed"),
        );
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::new(n_padded, 1);
        #[cfg(not(feature = "parallel"))]
        let (c1_bytes, c2_bytes, _g_rd, _h_rd, f_gens_blob) =
            read_ciphertexts_mk_raw(input_ciph_path).expect("read_ciphertexts_mk_raw failed");
        let t_gen = t_gen_start.elapsed();
 

        let t_decomp_start = Instant::now();
        #[cfg(feature = "parallel")]
        let (c1, c2, f_gens_rd) = {
            let ((r1, r2), r3) = rayon::join(
                || rayon::join(
                    || batch_decompress(&c1_bytes).expect("decompress c1 failed"),
                    || batch_decompress(&c2_bytes).expect("decompress c2 failed"),
                ),
                || batch_decompress(&f_gens_blob).expect("decompress f_gens failed"),
            );
            (r1, r2, r3)
        };
        #[cfg(not(feature = "parallel"))]
        let c1 = batch_decompress(&c1_bytes).expect("decompress c1 failed");
        #[cfg(not(feature = "parallel"))]
        let c2 = batch_decompress(&c2_bytes).expect("decompress c2 failed");
        #[cfg(not(feature = "parallel"))]
        let f_gens_rd = batch_decompress(&f_gens_blob).expect("decompress f_gens failed");
        let t_decomp = t_decomp_start.elapsed();
    

        let t_shuffle_start = Instant::now();
        let indices = generate_hetero_block_permutation(&p1_blocks, &mut rng);
        let c1_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c1[i]).collect();
        let c2_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c2[i]).collect();
        let t_shuffle = t_shuffle_start.elapsed();

        let t_rerand_start = Instant::now();
        #[cfg(all(feature = "parallel", not(feature = "production")))]
        let r_values: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
        #[cfg(not(feature = "parallel"))]
        let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

        let mut elem_block: Vec<usize> = Vec::with_capacity(n_input);
        for (ell, &gs) in p2_groups.iter().enumerate() {
            for _ in 0..gs { elem_block.push(ell); }
        }

        #[cfg(feature = "parallel")]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            c1p.par_iter_mut().zip(c2p.par_iter_mut())
                .zip(r_values.par_iter()).zip(elem_block.par_iter())
                .for_each(|(((a, b), r), &ell)| {
                    *a += &g_table * r;
                    *b += &f_tables[ell] * r;
                });
            (c1p, c2p)
        };
        #[cfg(not(feature = "parallel"))]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            for (j, r) in r_values.iter().enumerate() {
                c1p[j] += &g_table * r;
                c2p[j] += &f_tables[elem_block[j]] * r;
            }
            (c1p, c2p)
        };
        let t_rerand = t_rerand_start.elapsed();

        let t_e_start = Instant::now();
        let c1p_bytes = batch_compress(&c1_prime);
        let c2p_bytes = batch_compress(&c2_prime);
        let input_padded = derive_challenge_e(
            &pc_gens, &bp_gens,
            &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes,
            &f_gens_rd, &p1_blocks, &p2_groups, n_input, circuit_n,
        );
        let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Scalar::ZERO);

        let r_primes: Vec<Scalar> = {
            let mut off = 0usize;
            p2_groups.iter().map(|&gs| {
                let s = (off..off+gs)
                    .map(|j| r_values[j] * input_padded[indices[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                off += gs;
                -s
            }).collect()
        };
        let t_e = t_e_start.elapsed();

        let t_proof_start = Instant::now();
        let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1-mk");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens, &bp_gens, &mut prover_transcript,
            &input_padded, &output_padded,
            &c1_prime, &c2_prime, &f_gens_rd, &r_primes,
            k, d, &p1_blocks, &p2_groups, &mut rng,
        ).expect("Proof generation failed");
        let t_proof_gen = t_proof_start.elapsed();

        let t_write_start = Instant::now();
        let _output_size = write_proof_bundle(
            output_bundle_path, &proof, &out_commitment, &c1p_bytes, &c2p_bytes,
        ).expect("write_proof_bundle failed");
        let t_file_write = t_write_start.elapsed();

        let proof_size: usize = proof.to_bytes().len();

        // Let the CPU cool down before doing the Verifier
        std::thread::sleep(std::time::Duration::from_secs(30));

        // SINGLE-RUN VERIFIER

        let t_v_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let ((v_pc_gens, v_bp_gens), ((proof_r, out_commitment_r, c1p_bytes_r, c2p_bytes_r), (c1_orig_bytes, c2_orig_bytes, _g_v, _h_v, f_gens_v_blob))) =
            rayon::join(
                || rayon::join(|| PedersenGens::default(), || BulletproofGens::new(n_padded, 1)),
                || rayon::join(
                    || read_proof_bundle_raw(output_bundle_path).expect("read_proof_bundle_raw failed"),
                    || read_ciphertexts_mk_raw(input_ciph_path).expect("read_ciphertexts_mk_raw failed"),
                ),
            );
        #[cfg(not(feature = "parallel"))]
        let v_pc_gens = PedersenGens::default();
        #[cfg(not(feature = "parallel"))]
        let v_bp_gens = BulletproofGens::new(n_padded, 1);
        #[cfg(not(feature = "parallel"))]
        let (proof_r, out_commitment_r, c1p_bytes_r, c2p_bytes_r) =
            read_proof_bundle_raw(output_bundle_path).expect("read_proof_bundle_raw failed");
        #[cfg(not(feature = "parallel"))]
        let (c1_orig_bytes, c2_orig_bytes, _g_v, _h_v, f_gens_v_blob) =
            read_ciphertexts_mk_raw(input_ciph_path).expect("read_ciphertexts_mk_raw failed");
        
        
        let t_v_gen = t_v_gen_start.elapsed();
     
        let t_e_v_start = Instant::now();
        let f_gens_v_pts = batch_decompress(&f_gens_v_blob).expect("decompress f_gens failed");
        let input_padded_r = derive_challenge_e(
            &v_pc_gens, &v_bp_gens,
            &c1_orig_bytes, &c2_orig_bytes,
            &c1p_bytes_r, &c2p_bytes_r,
            &f_gens_v_pts, &p1_blocks, &p2_groups, n_input, circuit_n,
        );
        let t_e_v = t_e_v_start.elapsed();

        let e_original_r = &input_padded_r[..n_input];
       
        let c1_prime_c = blob_to_compressed(&c1p_bytes_r);
        let c2_prime_c = blob_to_compressed(&c2p_bytes_r);
        let c1_raw_c = blob_to_compressed(&c1_orig_bytes);
        let c2_raw_c = blob_to_compressed(&c2_orig_bytes);
        let f_gens_v_c = blob_to_compressed(&f_gens_v_blob);
        let t_verify_start = Instant::now();
        let mut verifier_transcript = Transcript::new(b"MAYA-Shuffle-v1-mk");
        let result = KShuffleGadget::verify(
            &v_pc_gens, &v_bp_gens, &mut verifier_transcript,
            &proof_r, &input_padded_r, out_commitment_r,
            &c1_prime_c, &c2_prime_c,
            &c1_raw_c, &c2_raw_c, e_original_r,
            &f_gens_v_c, &p1_blocks, &p2_groups,
        );
        assert!(result.is_ok(),
            "Verification failed N={}/k={}/d={}: {:?}", n_input, k, d, result.err());
        let t_verify = t_verify_start.elapsed();

        let ms = |dur: std::time::Duration| dur.as_secs_f64() * 1000.0;
        let total_prover   = ms(t_gen) + ms(t_decomp) + ms(t_table) + ms(t_shuffle) + ms(t_rerand)
                           + ms(t_e) + ms(t_proof_gen);
        let total_verifier = ms(t_v_gen) + ms(t_e_v) + ms(t_verify);
        let file_io        = ms(t_file_write);
        let thread_label   = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

        println!();
        println!("================================================================");
        println!("  Config [{}/{}]: N={}  L={}  ({})",
            i+1, configs.len(), n_input, l_cities, thread_label);
        for (ell, city) in cities.iter().enumerate() {
            println!("    Key {}: B={}  x={}  {}  => n={}",
                ell+1, city.voters, city.questions(), city.b_desc(), city.total_ciphertexts());
        }
        println!("================================================================");
        println!("  PROVER:");
       // println!("    Folding depth:           d={}  k_fold={}", d, k);
        println!("    CRS+DiskRead (wall):     {:>14.2} ms", ms(t_gen));
        println!("    Fixed-base tables:       {:>14.2} ms", ms(t_table));
        println!("    Batch decompress:        {:>14.2} ms", ms(t_decomp));
        println!("    Permutation:             {:>14.2} ms", ms(t_shuffle));
        println!("    Rerandomization:         {:>14.2} ms", ms(t_rerand));
        println!("    Challenge e derivation:  {:>14.2} ms", ms(t_e));
        println!("    Proof generation (*):    {:>14.2} ms", ms(t_proof_gen));
        println!("    File I/O (write only):   {:>14.2} ms", file_io);
        println!("    ─────────────────────────────────────────────────");
        println!("    Total E2E (incl. I/O):   {:>14.2} ms", total_prover + file_io);
        println!("  VERIFIER:");
        println!("    CRS+DiskRead (wall time):{:>14.2} ms", ms(t_v_gen));
        println!("    Challenge e derivation:  {:>14.2} ms", ms(t_e_v));
        println!("    Proof verification (*):  {:>14.2} ms", ms(t_verify));
        println!("    ────────────────────────────────────────────────");
        println!("    Total E2E:               {:>14.2} ms", total_verifier);
        println!("  Verification: PASSED");
        println!("  Proof size: {} bytes ({:.2} KB)", proof_size, proof_size as f64 / 1024.0);

        let b_summary = cities.iter()
            .map(|c| format!("{}x{}", c.voters, c.b_label()))
            .collect::<Vec<_>>()
            .join("+");

        let label_p = {
            let raw = format!("pi3/P/n{}/L{}/{}", n_input, l_cities, b_summary);
            if raw.len() > 90 { raw[..90].to_string() } else { raw }
        };
        let label_v = {
            let raw = format!("pi3/V/n{}/L{}/{}", n_input, l_cities, b_summary);
            if raw.len() > 90 { raw[..90].to_string() } else { raw }
        };
        
        if CRITERION_ENABLED {
            println!("  Proof generation time via Criterion ({} samples)...", SAMPLES);
       

        

        // CRITERION: Prover
        {
            let label = &label_p;
            let mut rng_b = rand::thread_rng();
            let c1_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let c2_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let idx_b = generate_hetero_block_permutation(&p1_blocks, &mut rng_b);
            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_b)).collect();
            #[cfg(feature = "parallel")]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                a.par_iter_mut().zip(bv.par_iter_mut()).zip(rv_b.par_iter()).zip(elem_block.par_iter())
                    .for_each(|(((x, y), r), &ell)| { *x += &g_table * r; *y += &f_tables[ell] * r; });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                for (j, r) in rv_b.iter().enumerate() { a[j] += &g_table * r; bv[j] += &f_tables[elem_block[j]] * r; }
                (a, bv)
            };
            let c1_b_bytes  = batch_compress(&c1_b);
            let c2_b_bytes  = batch_compress(&c2_b);
            let c1p_b_bytes = batch_compress(&c1p_b);
            let c2p_b_bytes = batch_compress(&c2p_b);
            let inp_b = derive_challenge_e(&pc_gens, &bp_gens,
                &c1_b_bytes, &c2_b_bytes, &c1p_b_bytes, &c2p_b_bytes,
                &f_gens, &p1_blocks, &p2_groups, n_input, circuit_n);
            let mut out_b: Vec<Scalar> = idx_b.iter().map(|&i| inp_b[i]).collect();
            out_b.resize(circuit_n, Scalar::ZERO);
            let rp_b: Vec<Scalar> = {
                let mut off = 0usize;
                p2_groups.iter().map(|&gs| {
                    let s = (off..off+gs)
                        .map(|j| rv_b[j] * inp_b[idx_b[j]])
                        .fold(Scalar::ZERO, |acc, x| acc + x);
                    off += gs;
                    -s
                }).collect()
            };

            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1-mk");
                    let mut brng = rand::thread_rng();
                    KShuffleGadget::prove(&pc_gens, &bp_gens, &mut t,
                        &inp_b, &out_b, &c1p_b, &c2p_b, &f_gens, &rp_b,
                        k, d, &p1_blocks, &p2_groups, &mut brng,
                    ).expect("prover bench failed");
                });
            });
        }
         }

        if CRITERION_ENABLED {
            println!("  Proof verification time via Criterion ({} samples)...", SAMPLES);
       

        // CRITERION: Verifier
        {
            let label = &label_v;
            let mut rng_v = rand::thread_rng();
            let c1_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let c2_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let idx_v = generate_hetero_block_permutation(&p1_blocks, &mut rng_v);
            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_v)).collect();
            #[cfg(feature = "parallel")]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                a.par_iter_mut().zip(bv.par_iter_mut()).zip(rv_v.par_iter()).zip(elem_block.par_iter())
                    .for_each(|(((x, y), r), &ell)| { *x += &g_table * r; *y += &f_tables[ell] * r; });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                for (j, r) in rv_v.iter().enumerate() { a[j] += &g_table * r; bv[j] += &f_tables[elem_block[j]] * r; }
                (a, bv)
            };
            let c1_v_bytes  = batch_compress(&c1_v);
            let c2_v_bytes  = batch_compress(&c2_v);
            let c1p_v_bytes = batch_compress(&c1p_v);
            let c2p_v_bytes = batch_compress(&c2p_v);
            let inp_v = derive_challenge_e(&pc_gens, &bp_gens,
                &c1_v_bytes, &c2_v_bytes, &c1p_v_bytes, &c2p_v_bytes,
                &f_gens, &p1_blocks, &p2_groups, n_input, circuit_n);
            let mut out_v: Vec<Scalar> = idx_v.iter().map(|&i| inp_v[i]).collect();
            out_v.resize(circuit_n, Scalar::ZERO);
            let rp_v: Vec<Scalar> = {
                let mut off = 0usize;
                p2_groups.iter().map(|&gs| {
                    let s = (off..off+gs)
                        .map(|j| rv_v[j] * inp_v[idx_v[j]])
                        .fold(Scalar::ZERO, |acc, x| acc + x);
                    off += gs;
                    -s
                }).collect()
            };
            let mut pt = Transcript::new(b"MAYA-Shuffle-v1-mk");
            let mut setup_rng = rand::thread_rng();
            let (proof_v, out_com_v) = KShuffleGadget::prove(
                &pc_gens, &bp_gens, &mut pt,
                &inp_v, &out_v, &c1p_v, &c2p_v, &f_gens, &rp_v,
                k, d, &p1_blocks, &p2_groups, &mut setup_rng,
            ).expect("prove for verifier bench failed");
            let e_v = &inp_v[..n_input];
        
            let c1p_v_c = blob_to_compressed(&c1p_v_bytes);
            let c2p_v_c = blob_to_compressed(&c2p_v_bytes);
            let c1_v_c = blob_to_compressed(&c1_v_bytes);
            let c2_v_c = blob_to_compressed(&c2_v_bytes);
            let f_gens_c = compress_all_par(&f_gens);

            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1-mk");
                    let res = KShuffleGadget::verify(
                        &pc_gens, &bp_gens, &mut t,
                        &proof_v, &inp_v, out_com_v,
                        &c1p_v_c, &c2p_v_c, &c1_v_c, &c2_v_c, e_v,
                        &f_gens_c, &p1_blocks, &p2_groups,
                    );
                    assert!(res.is_ok(), "verifier bench failed: {:?}", res.err());
                });
            });
        }
 }
        results.push(RunResult {
            n: n_input, k, d, l: l_cities,
            total_prover_ms: total_prover + file_io, total_verifier_ms: total_verifier,
            proof_bytes: proof_size, proof_gen_ms: ms(t_proof_gen), verify_ms: ms(t_verify),
            label_p, label_v,
        });
    }

    let thread_label = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };
    let read_criterion_mean_ms = |label: &str| -> Option<f64> {
        let json_path = format!("target/criterion/{}/new/estimates.json", label.replace('/', "_"));
        let content = std::fs::read_to_string(&json_path).ok()?;
        let mean_pos = content.find("\"mean\"")?;
        let after_mean = &content[mean_pos..];
        let pe_pos = after_mean.find("\"point_estimate\":")?;
        let val_str = &after_mean[pe_pos + "\"point_estimate\":".len()..];
        let val_end = val_str.find(|c: char| c == ',' || c == '}' || c == ' ').unwrap_or(val_str.len());
        let ns: f64 = val_str[..val_end].trim().parse().ok()?;
        Some(ns / 1_000_000.0)
    };
    let criterion_available = results.iter().any(|r| read_criterion_mean_ms(&r.label_p).is_some());

    println!();
    println!("================================================================");
    if criterion_available {
        println!("  Summary - {} (Criterion means)", thread_label);
    } else {
        println!("  Summary - {}", thread_label);
    }
    println!("================================================================");
    println!("  {:>10}  {:>4}  {:>16}  {:>16}  {:>13}",
        "N", "L", "Prover (ms)", "Verifier (ms)", "Proof (bytes)");
    println!("  {:->10}  {:->4}  {:->16}  {:->16}  {:->13}",
        "", "", "", "", "");
    for r in &results {
        let avg_p = read_criterion_mean_ms(&r.label_p)
            .map(|crit| crit + (r.total_prover_ms - r.proof_gen_ms))
            .unwrap_or(r.total_prover_ms);
        let avg_v = read_criterion_mean_ms(&r.label_v)
            .map(|crit| crit + (r.total_verifier_ms - r.verify_ms))
            .unwrap_or(r.total_verifier_ms);
        println!("  {:>10}  {:>4}  {:>16.2}  {:>16.2}  {:>13}",
            r.n, r.l, avg_p, avg_v, r.proof_bytes);
    }
    println!();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(SAMPLES)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = custom_benchmark
}

criterion_main!(benches);

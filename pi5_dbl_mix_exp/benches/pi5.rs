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


/// Number of benchmark samples
const SAMPLES: usize = 10;

const CRITERION_ENABLED: bool = true;

// Shuffle Gadget
struct KShuffleGadget;

impl KShuffleGadget {
    fn bind_statement(
        transcript: &mut HmacTranscript,
        k: usize,
        e_seed: &[u8; 32],
        k_original: usize,
        k_fold: usize,
        num_rounds: usize,
        num_blocks: usize,
        block_size: usize,
    ) {
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());
        transcript.append_message(b"statement", e_seed);
        transcript.append_message(b"n", &(k_original as u64).to_le_bytes());
        transcript.append_message(b"k_fold", &(k_fold as u64).to_le_bytes());
        transcript.append_message(b"d", &(num_rounds as u64).to_le_bytes());
        transcript.append_message(b"num_blocks", &(num_blocks as u64).to_le_bytes());
        transcript.append_message(b"block_size", &(block_size as u64).to_le_bytes());
    }

    fn fill_cs<CS: ConstraintSystem>(
        cs: &mut CS,
        x: &[Variable],
        y: &[Scalar],
        k_original: usize,
        num_blocks: usize,
        block_size: usize,
    ) {
       
        let z = cs.challenge_scalar(b"k-scalar shuffle challenge");
        let k = x.len(); 
        assert_eq!(x.len(), y.len());

        if num_blocks <= 1 {
            let mut prod_y = Scalar::ONE;
            for yi in y {
                prod_y *= *yi - z;
            }

            let mut prev_lc = if k_original == 0 {
                cs.constrain(x[0] - Scalar::ZERO);
                LinearCombination::from(-z)
            } else {
                x[0] - z
            };

            for i in 1..k {
                if i >= k_original {
                    cs.constrain(x[i] - Scalar::ZERO);
                    prev_lc = prev_lc * (-z);
                } else {
                    let term = x[i] - z;
                    let (_, _, out_var) = cs.multiply(prev_lc, term);
                    prev_lc = LinearCombination::from(out_var);
                }
            }
            cs.constrain(prev_lc - prod_y);
        } else {
            //Block-permutation check
            assert!(
                num_blocks * block_size == k_original,
                "num_blocks * block_size must equal k_original (got {} * {} = {} != {})",
                num_blocks, block_size, num_blocks * block_size, k_original
            );

            let v = cs.challenge_scalar(b"block-batch challenge v");

            let mut batched_rhs = Scalar::ZERO;
            let mut v_power = Scalar::ONE; 
            let mut batched_lhs = LinearCombination::from(Scalar::ZERO);

            for beta in 0..num_blocks {
                let start = beta * block_size;
                let end = start + block_size;

                let mut prod_y_block = Scalar::ONE;
                for i in start..end {
                    prod_y_block *= y[i] - z;
                }
                batched_rhs += v_power * prod_y_block;

                let mut prev_lc: LinearCombination = x[start] - z;
                for i in (start + 1)..end {
                    let term: LinearCombination = x[i] - z;
                    let (_, _, out_var) = cs.multiply(prev_lc, term);
                    prev_lc = LinearCombination::from(out_var);
                }

                batched_lhs = batched_lhs + prev_lc * v_power;

                v_power *= v;
            }

            for i in k_original..k {
                cs.constrain(x[i] - Scalar::ZERO);
            }

            cs.constrain(batched_lhs - batched_rhs);
        }
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut HmacTranscript,
        e_seed: &[u8; 32],
        input: &[Scalar],
        output: &[Scalar],
        c1_prime: &[RistrettoPoint],
        c2_prime: &[RistrettoPoint],
        r_prime: Scalar,
        k_fold: usize,
        num_rounds: usize,
        num_blocks: usize,
        block_size: usize,
        d1_prime: Option<&[RistrettoPoint]>,
        d2_prime: Option<&[RistrettoPoint]>,
        r_prime2: Option<Scalar>,
        alphas: Option<&[Scalar]>,
        d1_raw: Option<&[RistrettoPoint]>,
        d2_raw: Option<&[RistrettoPoint]>,
        alpha_pubs: Option<&[CompressedRistretto]>,
        rng: &mut (impl rand::RngCore + rand::CryptoRng),
    ) -> Result<(R1CSProof, CompressedRistretto), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }

        Self::bind_statement(
            transcript, k, e_seed, k_original, k_fold, num_rounds, num_blocks, block_size,
        );

        let dual_active = d1_prime.is_some() && d2_prime.is_some()
            && r_prime2.is_some() && alphas.is_some();
        if dual_active {
            if let Some(kpubs) = alpha_pubs {
                for kpub in kpubs {
                    transcript.commit_point(b"alpha_pub", kpub);
                }
            }
        }

        let mut prover = Prover::new(bp_gens, pc_gens, transcript);
        let v_blinding = Scalar::random(rng);
        let (output_commitment, output_vars) = prover.commit_vec(output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, num_blocks, block_size);
        let proof = cs.prove(
            c1_prime, c2_prime, r_prime, k_fold, num_rounds,
            d1_prime, d2_prime, r_prime2, alphas, d1_raw, d2_raw,
            Some(input), block_size,
        )?;
        Ok((proof, output_commitment))
    }

    pub fn verify<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut HmacTranscript,
        e_seed: &[u8; 32],
        k_fold: usize,
        num_rounds: usize,
        proof: &R1CSProof,
        input: &[Scalar],
        output_commitment: CompressedRistretto,
        c1_prime: &[CompressedRistretto],
        c2_prime: &[CompressedRistretto],
        c1_raw: &[CompressedRistretto],
        c2_raw: &[CompressedRistretto],
        e_challenge: &[Scalar],
        num_blocks: usize,
        block_size: usize,
        d1_prime: Option<&[CompressedRistretto]>,
        d2_prime: Option<&[CompressedRistretto]>,
        d1_raw: Option<&[CompressedRistretto]>,
        d2_raw: Option<&[CompressedRistretto]>,
        alpha_pubs: Option<&[CompressedRistretto]>,
    ) -> Result<(), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if num_blocks.checked_mul(block_size) != Some(k_original) {
            return Err(R1CSError::FormatError);
        }
        Self::bind_statement(
            transcript, k, e_seed, k_original, k_fold, num_rounds, num_blocks, block_size,
        );

        let dual_active = d1_prime.is_some() && d2_prime.is_some();
        if dual_active {
            if let Some(kpubs) = alpha_pubs {
                for kpub in kpubs {
                    transcript.commit_point(b"alpha_pub", kpub);
                }
            }
        }

        let mut verifier = Verifier::new(bp_gens, pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, num_blocks, block_size);
        cs.verify(
            proof, c1_prime, c2_prime, c1_raw, c2_raw, e_challenge,
            d1_prime, d2_prime, d1_raw, d2_raw,
            alpha_pubs, block_size, k_fold, num_rounds,
        )
    }
}

// Derive the challenge vector e deterministically from public parameters
fn derive_challenge_e(
    pc_gens: &PedersenGens,
    bp_gens: &BulletproofGens,
    c1_bytes: &[u8],
    c2_bytes: &[u8],
    c1p_bytes: &[u8],
    c2p_bytes: &[u8],
    d1_bytes: Option<&[u8]>,
    d2_bytes: Option<&[u8]>,
    d1p_bytes: Option<&[u8]>,
    d2p_bytes: Option<&[u8]>,
    anchor_bytes: Option<&[u8]>,
    num_blocks: usize,
    block_size: usize,
    n_original: usize,
    n_padded: usize,
) -> (Vec<Scalar>, [u8; 32]) {
    let verbose = std::env::var("VERBOSE").ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();
    let mut ts = Transcript::new(b"FiatShamir-e");
    ts.append_message(b"dom-sep", b"challenge-e-derivation");

    ts.commit_point(b"pk_g", &pc_gens.B.compress());
    ts.commit_point(b"pk_f", &pc_gens.F.compress());
    ts.commit_point(b"ck_h", &pc_gens.B_blinding.compress());

    <Transcript as TranscriptProtocol>::commit_u64(&mut ts, b"ck_n", bp_gens.gens_capacity as u64);
    ts.append_message(b"ck_g_seed", &bp_gens.G_seed);
    ts.append_message(b"ck_h_seed", &bp_gens.H_seed);

    let t_transcript = Instant::now();
    ts.append_message(b"c1",  c1_bytes);
    ts.append_message(b"c2",  c2_bytes);
    ts.append_message(b"c1p", c1p_bytes);
    ts.append_message(b"c2p", c2p_bytes);
    ts.append_message(b"num_blocks", &(num_blocks as u64).to_le_bytes());
    ts.append_message(b"block_size", &(block_size as u64).to_le_bytes());
    if d1_bytes.is_some() {
        ts.commit_point(b"pk_f2", &pc_gens.F2.compress());
    }
    if let Some(bytes) = d1_bytes {
        ts.append_message(b"d1", bytes);
    }
    if let Some(bytes) = d2_bytes {
        ts.append_message(b"d2", bytes);
    }
    if let Some(bytes) = d1p_bytes {
        ts.append_message(b"d1p", bytes);
    }
    if let Some(bytes) = d2p_bytes {
        ts.append_message(b"d2p", bytes);
    }
    if let Some(bytes) = anchor_bytes {
        ts.append_message(b"K_anchors", bytes); // per-voter K_beta 
    }
    if verbose {
        eprintln!(
            "[derive_e] n={}: transcript feed 4N bytes: {:?}",
            n_original,
            t_transcript.elapsed()
        );
    }

    let t_expand = Instant::now();
    let mut seed = [0u8; 32];
    ts.challenge_bytes(b"e_seed", &mut seed);
    let e_seed = seed;

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
    if verbose {
        eprintln!(
            "[derive_e] n={}: seed-squeeze + scalar expand: {:?}",
            n_original,
            t_expand.elapsed()
        );
    }

    (e, e_seed)
}


// File I/O Helpers
fn encode_ciphertexts(
    c1: &[RistrettoPoint],
    c2: &[RistrettoPoint],
    d1: &[RistrettoPoint],
    d2: &[RistrettoPoint],
    g: &RistrettoPoint,
    f: &RistrettoPoint,
    f2: &RistrettoPoint,
    h: &RistrettoPoint,
) -> Vec<u8> {
    let n = c1.len();
    assert_eq!(n, c2.len());
    assert_eq!(n, d1.len());
    assert_eq!(n, d2.len());
    let mut buf = Vec::with_capacity(8 + (4 * n + 4) * 32);
    buf.extend_from_slice(&(n as u64).to_le_bytes());

    #[cfg(feature = "parallel")]
    {
        let (c1_blob, c2_blob) = rayon::join(|| batch_compress(c1), || batch_compress(c2));
        let (d1_blob, d2_blob) = rayon::join(|| batch_compress(d1), || batch_compress(d2));
        buf.extend_from_slice(&c1_blob);
        buf.extend_from_slice(&c2_blob);
        buf.extend_from_slice(&d1_blob);
        buf.extend_from_slice(&d2_blob);
    }
    #[cfg(not(feature = "parallel"))]
    for pt in c1.iter().chain(c2.iter()).chain(d1.iter()).chain(d2.iter()) {
        buf.extend_from_slice(pt.compress().as_bytes());
    }

    buf.extend_from_slice(g.compress().as_bytes());
    buf.extend_from_slice(f.compress().as_bytes());
    buf.extend_from_slice(f2.compress().as_bytes());
    buf.extend_from_slice(h.compress().as_bytes());
    buf
}

// Store the received input list to disk 
fn store_bytes(path: &str, bytes: &[u8]) -> std::io::Result<usize> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(bytes)?;
    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(bytes.len())
}


#[allow(dead_code)]
fn write_scalars(path: &str, scalars: &[Scalar]) -> std::io::Result<()> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);
    w.write_all(&(scalars.len() as u64).to_le_bytes())?;
    for s in scalars {
        w.write_all(s.as_bytes())?;
    }
    w.flush()?;
    let f = w.into_inner()?;
    f.sync_all()?;
    Ok(())
}

#[allow(dead_code)]
fn read_scalars(path: &str) -> std::io::Result<Vec<Scalar>> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;
    let mut out = Vec::with_capacity(n);
    let mut buf32 = [0u8; 32];
    for _ in 0..n {
        r.read_exact(&mut buf32)?;
        let s = Scalar::from_canonical_bytes(buf32)
            .into_option()
            .ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid scalar bytes")
            })?;
        out.push(s);
    }
    Ok(out)
}


fn batch_compress(points: &[RistrettoPoint]) -> Vec<u8> {
    let mut blob = vec![0u8; points.len() * 32];
    #[cfg(feature = "parallel")]
    blob.par_chunks_exact_mut(32)
        .zip(points.par_iter())
        .for_each(|(chunk, pt)| chunk.copy_from_slice(pt.compress().as_bytes()));
    #[cfg(not(feature = "parallel"))]
    for (chunk, pt) in blob.chunks_exact_mut(32).zip(points.iter()) {
        chunk.copy_from_slice(pt.compress().as_bytes());
    }
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

fn batch_decompress(blob: &[u8]) -> std::io::Result<Vec<RistrettoPoint>> {
    assert_eq!(
        blob.len() % 32,
        0,
        "blob length must be a multiple of 32 bytes"
    );
    #[cfg(feature = "parallel")]
    {
        blob.par_chunks(32)
            .map(|chunk| {
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })
            })
            .collect()
    }
    #[cfg(not(feature = "parallel"))]
    {
        let mut out = Vec::with_capacity(blob.len() / 32);
        for chunk in blob.chunks(32) {
            out.push(
                CompressedRistretto::from_slice(chunk)
                    .map_err(|e| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e))
                    })?
                    .decompress()
                    .ok_or_else(|| {
                        std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed")
                    })?,
            );
        }
        Ok(out)
    }
}

fn generate_block_permutation(
    num_blocks: usize,
    block_size: usize,
    rng: &mut impl rand::RngCore,
) -> Vec<usize> {
    let n = num_blocks * block_size;
    let mut indices: Vec<usize> = (0..n).collect();
    for beta in 0..num_blocks {
        let start = beta * block_size;
        let end = start + block_size;
        indices[start..end].shuffle(rng);
    }
    indices
}

fn write_proof_bundle(
    path: &str,
    proof: &R1CSProof,
    out_commitment: &CompressedRistretto,
    anchor_blob: &[u8],
    c1p_blob: &[u8],
    c2p_blob: &[u8],
    d1p_blob: &[u8],
    d2p_blob: &[u8],
) -> std::io::Result<usize> {
    let file = File::create(path)?;
    let mut w = BufWriter::new(file);

    let proof_bytes = proof.to_bytes();

    w.write_all(&(proof_bytes.len() as u64).to_le_bytes())?;
    w.write_all(&proof_bytes)?;

    w.write_all(out_commitment.as_bytes())?;

    for blob in &[anchor_blob, c1p_blob, c2p_blob, d1p_blob, d2p_blob] {
        let cnt = blob.len() / 32;
        w.write_all(&(cnt as u64).to_le_bytes())?;
        w.write_all(blob)?;
    }

    w.flush()?;
    let f = w.into_inner()?;
    f.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}



fn read_ciphertexts_raw(path: &str) -> std::io::Result<(
    Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>,
    RistrettoPoint, RistrettoPoint, RistrettoPoint, RistrettoPoint,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

    let mut blob = vec![0u8; 4 * n * 32];
    r.read_exact(&mut blob)?;
    let s = n * 32;
    let c1_raw = blob[..s].to_vec();
    let c2_raw = blob[s..2*s].to_vec();
    let d1_raw = blob[2*s..3*s].to_vec();
    let d2_raw = blob[3*s..].to_vec();

    let mut buf32 = [0u8; 32];
    let decomp = |b: [u8; 32], label: &'static str| -> std::io::Result<RistrettoPoint> {
        CompressedRistretto::from_slice(&b)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
            .decompress()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("decompress {} failed", label)))
    };
    r.read_exact(&mut buf32)?; let g = decomp(buf32, "g")?;
    r.read_exact(&mut buf32)?; let f = decomp(buf32, "f")?;
    r.read_exact(&mut buf32)?; let f2 = decomp(buf32, "f2")?;
    r.read_exact(&mut buf32)?; let h = decomp(buf32, "h")?;

    Ok((c1_raw, c2_raw, d1_raw, d2_raw, g, f, f2, h))
}

fn read_proof_bundle_raw(path: &str) -> std::io::Result<(
    R1CSProof, CompressedRistretto, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>,
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

    let anchor_blob = read_blob(&mut r)?;
    let c1p_blob = read_blob(&mut r)?;
    let c2p_blob = read_blob(&mut r)?;
    let d1p_blob = read_blob(&mut r)?;
    let d2p_blob = read_blob(&mut r)?;

    Ok((proof, out_commitment, anchor_blob, c1p_blob, c2p_blob, d1p_blob, d2p_blob))
}

// Table: Prover and Verifier Performance
#[allow(unused_variables)]
fn custom_benchmark(c: &mut Criterion) {
    let quick_mode = std::env::var("QUICK")
        .ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();

    // (n_input, k_fold, num_blocks, block_size); num_blocks * block_size = n_input
    let configs: &[(usize, usize, usize, usize)] = if quick_mode {
        &[(1_000, 4, 10, 100)]
    } else {
        &[
            (200000, 4, 10000, 20),
            (100000, 4, 5000, 20),
           // (500000, 4, 500, 1000),
        ]
    };

    let features = {
        let mut fv = Vec::new();
        if cfg!(feature = "parallel") {
            fv.push("parallel");
        }
        if fv.is_empty() {
            fv.push("none");
        }
        fv.join(", ")
    };

    println!();
    println!("================================================================");
    println!("  Pi_5 benchmark: shuffle-and-exponentiate (DbleMixExp)");
    println!("  Configurations ({} total):", configs.len());
    println!("  * NOTE: This is a Dual-Shuffle. The total ciphertexts processed is 2 * N.");
    for (idx, &(n, k, nb, bs)) in configs.iter().enumerate() {
        println!("    {:>2}.  N = {:>9}   B = {}   b = {}", idx + 1, n, nb, bs);
    }
    println!("  Features: {}", features);
    println!("================================================================");

    let input_ciph_path = "./maya_ristretto_pi5_input_ciph.bin";
    let output_bundle_path = "./maya_ristretto_pi5_output_bundle.bin";

    struct RunResult {
        n: usize,
        k: usize,
        d: usize,
        num_blocks: usize,
        block_size: usize,
        total_prover_ms: f64,
        total_verifier_ms: f64,
        proof_bytes: usize,
        proof_gen_ms: f64,
        verify_ms: f64,
    }
    let mut results: Vec<RunResult> = Vec::new();

    for (i, &(n_input, k, num_blocks, block_size)) in configs.iter().enumerate() {
        assert_eq!(
            num_blocks * block_size, n_input,
            "num_blocks ({}) * block_size ({}) must equal n_input ({})",
            num_blocks, block_size, n_input
        );
        let n_padded = n_input + (k - 1) + 1; //+1 for a safe margin

        // Setup
        let pc_gens_setup = PedersenGens::default();

        let mut rng = rand::thread_rng();

        let rem = n_input % k;
        let circuit_n = if rem == 0 {
            n_input
        } else {
            n_input + (k - rem)
        };

        let mut n_j = circuit_n;
        let mut d = 0usize;
        while n_j > 1 {
            let r = n_j % k;
            let p = if r == 0 { 0 } else { k - r };
            n_j = (n_j + p) / k;
            d += 1;
        }
        let m_final = n_j; 

        let mut total_pad = 0usize;
        let mut nj2 = n_input;
        for _ in 0..d {
            let r = nj2 % k;
            let p = if r == 0 { 0 } else { k - r };
            total_pad += p;
            nj2 = (nj2 + p) / k;
        }
        let padding_pct = total_pad as f64 / n_input as f64 * 100.0;


        // Input generation
        let c1_gen: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let c2_gen: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let d1_gen: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();
        let d2_gen: Vec<RistrettoPoint> = (0..n_input)
            .map(|_| RistrettoPoint::random(&mut rng))
            .collect();

        // Untimed:  Generating and compressing it is not mixer work: the mixer receives the list from the bulletin board / previous mixer.
        let input_blob = encode_ciphertexts(
            &c1_gen,
            &c2_gen,
            &d1_gen,
            &d2_gen,
            &pc_gens_setup.B,
            &pc_gens_setup.F,
            &pc_gens_setup.F2,
            &pc_gens_setup.B_blinding,
        );
        drop((c1_gen, c2_gen, d1_gen, d2_gen));

        // SINGLE-RUN PROVER

        // [0] Store the received input list to disk 
        let t_store_start = Instant::now();
        let input_file_size = store_bytes(input_ciph_path, &input_blob).expect("store input failed");
        let t_store = t_store_start.elapsed();
        drop(input_blob);

        // [1] CRS generation + disk read
        let t_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let ((pc_gens, bp_gens), (c1_bytes, c2_bytes, d1_bytes_rd, d2_bytes_rd, _g_rd, _f_rd, _f2_rd, _h_rd)) = rayon::join(
            || rayon::join(|| PedersenGens::default(), || BulletproofGens::new(n_padded, 1)),
            || read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed"),
        );
        #[cfg(not(feature = "parallel"))]
        let pc_gens = PedersenGens::default();
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::new(n_padded, 1);
        #[cfg(not(feature = "parallel"))]
        let (c1_bytes, c2_bytes, d1_bytes_rd, d2_bytes_rd, _g_rd, _f_rd, _f2_rd, _h_rd) =
            read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed");
        let t_gen = t_gen_start.elapsed();

        let g = pc_gens.B;
        let f = pc_gens.F;
        let f2 = pc_gens.F2;

        let t_table_start = Instant::now();
        let g_table = RistrettoBasepointTable::create(&g);
        let f_table = RistrettoBasepointTable::create(&f);
        let f2_table = RistrettoBasepointTable::create(&f2);
        let t_table = t_table_start.elapsed();
        let table_size_bytes = std::mem::size_of::<RistrettoBasepointTable>();

        // Decompress both key groups read from disk (C1, C2 and D1, D2).
        let t_decomp_start = Instant::now();
        #[cfg(feature = "parallel")]
        let ((c1, c2), (d1_raw, d2_raw)) = rayon::join(
            || rayon::join(
                || batch_decompress(&c1_bytes).expect("decompress c1 failed"),
                || batch_decompress(&c2_bytes).expect("decompress c2 failed"),
            ),
            || rayon::join(
                || batch_decompress(&d1_bytes_rd).expect("decompress d1 failed"),
                || batch_decompress(&d2_bytes_rd).expect("decompress d2 failed"),
            ),
        );
        #[cfg(not(feature = "parallel"))]
        let c1 = batch_decompress(&c1_bytes).expect("decompress c1 failed");
        #[cfg(not(feature = "parallel"))]
        let c2 = batch_decompress(&c2_bytes).expect("decompress c2 failed");
        #[cfg(not(feature = "parallel"))]
        let d1_raw = batch_decompress(&d1_bytes_rd).expect("decompress d1 failed");
        #[cfg(not(feature = "parallel"))]
        let d2_raw = batch_decompress(&d2_bytes_rd).expect("decompress d2 failed");
        let t_decomp = t_decomp_start.elapsed();

        // [2] Permutation
        let t_shuffle_start = Instant::now();
        let indices: Vec<usize> = if num_blocks > 1 {
            generate_block_permutation(num_blocks, block_size, &mut rng)
        } else {
            let mut idx: Vec<usize> = (0..n_input).collect();
            idx.shuffle(&mut rng);
            idx
        };
        let c1_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c1[i]).collect();
        let c2_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c2[i]).collect();
        let t_shuffle = t_shuffle_start.elapsed();

        // [3a] Rerandomization of C (first group)
        let t_rerand_start = Instant::now();

        let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

        #[cfg(feature = "parallel")]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            c1p.par_iter_mut()
                .zip(c2p.par_iter_mut())
                .zip(r_values.par_iter())
                .for_each(|((a, b), r)| {
                    *a += &g_table * r;
                    *b += &f_table * r;
                });
            (c1p, c2p)
        };
        #[cfg(not(feature = "parallel"))]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            for (j, r) in r_values.iter().enumerate() {
                c1p[j] += &g_table * r;
                c2p[j] += &f_table * r;
            }
            (c1p, c2p)
        };

        let t_rerand = t_rerand_start.elapsed();

        // [3b] Rerandomization for D (second group)
        let t_rerand2_start = Instant::now();
        let r2_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();
        // Per-voter alpha: one alpha_beta per block (voter), anchor K_beta = g^{alpha_beta}.
        let alphas: Vec<Scalar> = (0..num_blocks).map(|_| Scalar::random(&mut rng)).collect();
        let alpha_pubs: Vec<RistrettoPoint> = alphas.iter().map(|a| &g_table * a).collect();

       
        let d1_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| d1_raw[i]).collect();
        let d2_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| d2_raw[i]).collect();

        #[cfg(feature = "parallel")]
        let (d1_prime, d2_prime): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
            let mut d1p = d1_prime_init;
            let mut d2p = d2_prime_init;
            d1p.par_iter_mut()
                .zip(d2p.par_iter_mut())
                .zip(r2_values.par_iter())
                .enumerate()
                .for_each(|(j, ((a, b), r2))| {
                    let alpha = alphas[j / block_size];
                    *a = &*a * alpha + &g_table * r2;
                    *b = &*b * alpha + &f2_table * r2;
                });
            (d1p, d2p)
        };
        #[cfg(not(feature = "parallel"))]
        let (d1_prime, d2_prime): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
            let mut d1p = d1_prime_init;
            let mut d2p = d2_prime_init;
            for (j, r2) in r2_values.iter().enumerate() {
                let alpha = alphas[j / block_size];
                d1p[j] = &d1p[j] * alpha + &g_table * r2;
                d2p[j] = &d2p[j] * alpha + &f2_table * r2;
            }
            (d1p, d2p)
        };

        let t_rerand2 = t_rerand2_start.elapsed();

        // [4a] Challenge e derivation
        let t_e_derive_p_start = Instant::now();
        let c1p_bytes = batch_compress(&c1_prime);
        let c2p_bytes = batch_compress(&c2_prime);
        let d1p_bytes = batch_compress(&d1_prime);
        let d2p_bytes = batch_compress(&d2_prime);
        let anchor_bytes = batch_compress(&alpha_pubs);
        let alpha_pubs_c = blob_to_compressed(&anchor_bytes);
        let (input_padded, e_seed) = derive_challenge_e(
            &pc_gens, &bp_gens,
            &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes,
            Some(&d1_bytes_rd), Some(&d2_bytes_rd),
            Some(&d1p_bytes), Some(&d2p_bytes), Some(&anchor_bytes),
            num_blocks, block_size,
            n_input, circuit_n,
        );
        let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Scalar::ZERO);
        let r_prime: Scalar = {
            let s = (0..n_input)
                .map(|j| r_values[j] * input_padded[indices[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x);
            -s
        };
        #[cfg(feature = "parallel")]
        let r_prime2: Scalar = {
            let s: Scalar = (0..n_input).into_par_iter()
                .map(|j| r2_values[j] * input_padded[indices[j]])
                .sum();
            -s
        };
        #[cfg(not(feature = "parallel"))]
        let r_prime2: Scalar = {
            let s = (0..n_input)
                .map(|j| r2_values[j] * input_padded[indices[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x);
            -s
        };
        let e_original = &input_padded[..n_input];
        let t_e_derive_p = t_e_derive_p_start.elapsed();


        // [5] Proof generation
        let t_proof_start = Instant::now();
        let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens,
            &bp_gens,
            &mut prover_transcript,
            &e_seed,
            &input_padded,
            &output_padded,
            &c1_prime,
            &c2_prime,
            r_prime,
            k,
            d,
            num_blocks, block_size,
            Some(&d1_prime), Some(&d2_prime),
            Some(r_prime2), Some(&alphas),
            Some(&d1_raw), Some(&d2_raw),
            Some(&alpha_pubs_c),
            &mut rng,
        )
        .expect("Proof generation failed");
        let t_proof_gen = t_proof_start.elapsed();

        // [6] Write proof bundle
        let t_write_start = Instant::now();
        let output_file_size = write_proof_bundle(
            output_bundle_path,
            &proof,
            &out_commitment,
            &anchor_bytes,
            &c1p_bytes,
            &c2p_bytes,
            &d1p_bytes,
            &d2p_bytes,
        )
        .expect("write_proof_bundle failed");
        let t_file_write = t_write_start.elapsed();

        let proof_size: usize = proof.to_bytes().len();

        // Let the CPU cool down before doing the Verifier
        std::thread::sleep(std::time::Duration::from_secs(30));

        // SINGLE-RUN VERIFIER

        // [1] Verifier regenerates CRS 
        let t_v_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let ((v_pc_gens, v_bp_gens), ((proof_r, out_commitment_r, anchor_r_bytes, c1p_r_bytes, c2p_r_bytes, d1p_r_bytes, d2p_r_bytes), (c1_orig_bytes, c2_orig_bytes, d1_orig_bytes, d2_orig_bytes, _g_v, _f_v, _f2_v, _h_v))) =
            rayon::join(
                || rayon::join(|| PedersenGens::default(), || BulletproofGens::new(n_padded, 1)),
                || rayon::join(
                    || read_proof_bundle_raw(output_bundle_path).expect("read_proof_bundle_raw failed"),
                    || read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed"),
                ),
            );
        #[cfg(not(feature = "parallel"))]
        let v_pc_gens = PedersenGens::default();
        #[cfg(not(feature = "parallel"))]
        let v_bp_gens = BulletproofGens::new(n_padded, 1);
        #[cfg(not(feature = "parallel"))]
        let (proof_r, out_commitment_r, anchor_r_bytes, c1p_r_bytes, c2p_r_bytes, d1p_r_bytes, d2p_r_bytes) =
            read_proof_bundle_raw(output_bundle_path).expect("read_proof_bundle_raw failed");
        #[cfg(not(feature = "parallel"))]
        let (c1_orig_bytes, c2_orig_bytes, d1_orig_bytes, d2_orig_bytes, _g_v, _f_v, _f2_v, _h_v) =
            read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed");
        let t_v_gen = t_v_gen_start.elapsed();
       
        // [2] Derive e
        let t_e_start = Instant::now();
        let (input_padded_r, e_seed_r) = derive_challenge_e(
            &v_pc_gens,
            &v_bp_gens,
            &c1_orig_bytes,
            &c2_orig_bytes,
            &c1p_r_bytes,
            &c2p_r_bytes,
            Some(&d1_orig_bytes),
            Some(&d2_orig_bytes),
            Some(&d1p_r_bytes),
            Some(&d2p_r_bytes),
            Some(&anchor_r_bytes),
            num_blocks, block_size,
            n_input,
            circuit_n,
        );
        let t_e_derive = t_e_start.elapsed();

        // [3] Verify
        let e_original_r = &input_padded_r[..n_input];

        let t_parse_start = Instant::now();
        let c1_prime_c = blob_to_compressed(&c1p_r_bytes);
        let c2_prime_c = blob_to_compressed(&c2p_r_bytes);
        let c1_raw_c = blob_to_compressed(&c1_orig_bytes);
        let c2_raw_c = blob_to_compressed(&c2_orig_bytes);
        let d1_prime_c = blob_to_compressed(&d1p_r_bytes);
        let d2_prime_c = blob_to_compressed(&d2p_r_bytes);
        let d1_raw_c = blob_to_compressed(&d1_orig_bytes);
        let d2_raw_c = blob_to_compressed(&d2_orig_bytes);
        let anchors_r_c = blob_to_compressed(&anchor_r_bytes);
        let t_parse = t_parse_start.elapsed();

        let t_verify_start = Instant::now();
        let mut verifier_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let result = KShuffleGadget::verify(
            &v_pc_gens,
            &v_bp_gens,
            &mut verifier_transcript,
            &e_seed_r,
            k,
            d,
            &proof_r,
            &input_padded_r,
            out_commitment_r,
            &c1_prime_c,
            &c2_prime_c,
            &c1_raw_c,
            &c2_raw_c,
            e_original_r,
            num_blocks, block_size,
            Some(&d1_prime_c), Some(&d2_prime_c),
            Some(&d1_raw_c), Some(&d2_raw_c),
            Some(&anchors_r_c),
        );
        assert!(
            result.is_ok(),
            "Verification failed N={}/k={}/d={}: {:?}",
            n_input, k, d, result.err()
        );
        let t_verify = t_verify_start.elapsed();

        // PRINT TIMINGS
        let ms = |dur: std::time::Duration| dur.as_secs_f64() * 1000.0;
        let t_gen_ms = ms(t_gen);
        let t_store_ms = ms(t_store);
        let t_decomp_ms = ms(t_decomp);
        let t_table_ms = ms(t_table);
        let t_shuffle_ms = ms(t_shuffle);
        let t_rerand_ms = ms(t_rerand);
        let t_rerand2_ms = ms(t_rerand2);
        let t_e_derive_p_ms = ms(t_e_derive_p);
        let t_proof_gen_ms = ms(t_proof_gen);
        let t_file_write_ms = ms(t_file_write);
        let t_v_gen_ms = ms(t_v_gen);
        let t_e_derive_ms = ms(t_e_derive);
        let t_verify_ms = ms(t_verify);
        let t_parse_ms = ms(t_parse);
        let total_prover = t_store_ms + t_gen_ms + t_decomp_ms + t_table_ms + t_shuffle_ms + t_rerand_ms
            + t_rerand2_ms + t_e_derive_p_ms + t_proof_gen_ms;
        let file_io = t_file_write_ms;
        let total_prover_e2e = total_prover + file_io;
        let total_verifier = t_v_gen_ms + t_e_derive_ms + t_parse_ms + t_verify_ms;
        let total_verifier_e2e = total_verifier;
        let proof_kb = proof_size as f64 / 1024.0;
        let thread_label = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

        println!();
        println!("================================================================");
        println!(
            "  Config [{}/{}]: N={:>9}  B={}  b={}  ({})",
            i + 1, configs.len(), n_input, num_blocks, block_size, thread_label
        );
        println!("================================================================");
        println!();
        println!("  Single-run timings (one pass for quick timing):");
        println!();
        println!("  PROVER:");
        println!("    Store input (write + fsync):  {:>14.2} ms", t_store_ms);
        println!("    CRS + DiskRead (wall time):     {:>14.2} ms", t_gen_ms);
        println!("    Fixed-base table:             {:>14.2} ms", t_table_ms);
        println!("    Batch decompress C1+C2+D1+D2: {:>14.2} ms", t_decomp_ms);
        println!("    Permutation:                  {:>14.2} ms", t_shuffle_ms);
        println!("    Rerandomization (C):          {:>14.2} ms", t_rerand_ms);
        println!("    Rerandomization (D):          {:>14.2} ms", t_rerand2_ms);
        println!("    Challenge e derivation:       {:>14.2} ms", t_e_derive_p_ms);
        println!("    Proof generation (*):         {:>14.2} ms", t_proof_gen_ms);
        println!("    File I/O (write only):        {:>14.2} ms", file_io);
        println!("    ─────────────────────────────────────────────────");
        println!("    Total E2E (incl. I/O):        {:>14.2} ms", total_prover_e2e);
        println!();
        println!();
        println!("  VERIFIER:");
        println!("    CRS + DiskRead (wall time):     {:>14.2} ms", t_v_gen_ms);
        println!("    Challenge e derivation:       {:>14.2} ms", t_e_derive_ms);
        println!("    Parse compressed points:      {:>14.2} ms", t_parse_ms);
        println!("    Proof verification (*):       {:>14.2} ms", t_verify_ms);
        println!("    ────────────────────────────────────────────────");
        println!("    Total E2E:                    {:>14.2} ms", total_verifier_e2e);
        println!();
        println!("  Verification: PASSED");
        println!("  Proof size: {} bytes ({:.2} KB)", proof_size, proof_kb);
        println!();
        println!();
        if CRITERION_ENABLED {
            println!("  (*) Proof generation and verification times can vary across runs");
            println!("     due to variable-time multi-scalar multiplications. Computing");
            println!("     their average over multiple samples for more stable estimates:");
            println!();
            println!("  Proof generation time via Criterions ({} samples, adjust SAMPLES if needed)...", SAMPLES);
       

        // CRITERION: Prover
        {
            let label = format!("pi5/P/n={}/B={}/b={}", n_input, num_blocks, block_size);

            let mut rng_b = rand::thread_rng();
            let c1_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let c2_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let d1_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let d2_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let alphas_b: Vec<Scalar> = (0..num_blocks).map(|_| Scalar::random(&mut rng_b)).collect();
            let alpha_pubs_b: Vec<RistrettoPoint> = alphas_b.iter().map(|a| &g_table * a).collect();
            let anchor_b_bytes = batch_compress(&alpha_pubs_b);
            let alpha_pubs_b_c = blob_to_compressed(&anchor_b_bytes);

            let idx_b: Vec<usize> = if num_blocks > 1 {
                generate_block_permutation(num_blocks, block_size, &mut rng_b)
            } else {
                let mut idx: Vec<usize> = (0..n_input).collect();
                idx.shuffle(&mut rng_b);
                idx
            };

            let rv_b: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_b)).collect();
            let rv2_b: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_b)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                a.par_iter_mut().zip(bv.par_iter_mut()).zip(rv_b.par_iter())
                    .for_each(|((x, y), r)| { *x += &g_table * r; *y += &f_table * r; });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_b, c2p_b) = {
                let mut a: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c1_b[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_b.iter().map(|&i| c2_b[i]).collect();
                for (j, r) in rv_b.iter().enumerate() { a[j] += &g_table * r; bv[j] += &f_table * r; }
                (a, bv)
            };

            #[cfg(feature = "parallel")]
            let (d1p_b, d2p_b): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
                let (d1s, d2s): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) =
                    d1_b.par_iter().zip(d2_b.par_iter()).enumerate()
                        .map(|(i, (p1, p2))| { let a = alphas_b[i / block_size]; (p1 * a, p2 * a) })
                        .unzip();
                idx_b.par_iter().zip(rv2_b.par_iter())
                    .map(|(&i, r2)| (d1s[i] + &g_table * r2, d2s[i] + &f2_table * r2))
                    .unzip()
            };
            #[cfg(not(feature = "parallel"))]
            let (d1p_b, d2p_b): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
                let (d1s, d2s): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) =
                    d1_b.iter().zip(d2_b.iter()).enumerate()
                        .map(|(i, (p1, p2))| { let a = alphas_b[i / block_size]; (p1 * a, p2 * a) })
                        .unzip();
                idx_b.iter().zip(rv2_b.iter())
                    .map(|(&i, r2)| (d1s[i] + &g_table * r2, d2s[i] + &f2_table * r2))
                    .unzip()
            };

            let c1_b_bytes = batch_compress(&c1_b);
            let c2_b_bytes = batch_compress(&c2_b);
            let d1_b_bytes = batch_compress(&d1_b);
            let d2_b_bytes = batch_compress(&d2_b);
            let c1p_b_bytes = batch_compress(&c1p_b);
            let c2p_b_bytes = batch_compress(&c2p_b);
            let d1p_b_bytes = batch_compress(&d1p_b);
            let d2p_b_bytes = batch_compress(&d2p_b);

            let (inp_b, e_seed_b) = derive_challenge_e(
                &pc_gens, &bp_gens,
                &c1_b_bytes, &c2_b_bytes, &c1p_b_bytes, &c2p_b_bytes,
                Some(&d1_b_bytes), Some(&d2_b_bytes), Some(&d1p_b_bytes), Some(&d2p_b_bytes), Some(&anchor_b_bytes),
                num_blocks, block_size, n_input, circuit_n,
            );
            let mut out_b: Vec<Scalar> = idx_b.iter().map(|&i| inp_b[i]).collect();
            out_b.resize(circuit_n, Scalar::ZERO);
            let rp_b: Scalar = {
                let s = (0..n_input).map(|j| rv_b[j] * inp_b[idx_b[j]]).fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };
            let rp2_b: Scalar = {
                let s = (0..n_input).map(|j| rv2_b[j] * inp_b[idx_b[j]]).fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };
            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let mut bench_rng = rand::thread_rng();
                    KShuffleGadget::prove(
                        &pc_gens, &bp_gens, &mut t, &e_seed_b,
                        &inp_b, &out_b, &c1p_b, &c2p_b, rp_b, k, d,
                        num_blocks, block_size,
                        Some(&d1p_b), Some(&d2p_b),
                        Some(rp2_b), Some(&alphas_b),
                        Some(&d1_b), Some(&d2_b),
                        Some(&alpha_pubs_b_c),
                        &mut bench_rng,
                    )
                    .expect("prover bench failed");
                });
            });
        }
         }

        if CRITERION_ENABLED {
            println!("  Proof verification time via Criterions ({} samples, adjust SAMPLES if needed)...", SAMPLES);
       

        // CRITERION: Verifier
        {
            let label = format!("pi5/V/n={}/B={}/b={}", n_input, num_blocks, block_size);

            let mut rng_v = rand::thread_rng();
            let c1_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let c2_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let d1_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let d2_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let alphas_v: Vec<Scalar> = (0..num_blocks).map(|_| Scalar::random(&mut rng_v)).collect();
            let alpha_pubs_v: Vec<RistrettoPoint> = alphas_v.iter().map(|a| &g_table * a).collect();
            let anchor_v_bytes = batch_compress(&alpha_pubs_v);
            let alpha_pubs_v_c = blob_to_compressed(&anchor_v_bytes);

            let idx_v: Vec<usize> = if num_blocks > 1 {
                generate_block_permutation(num_blocks, block_size, &mut rng_v)
            } else {
                let mut idx: Vec<usize> = (0..n_input).collect();
                idx.shuffle(&mut rng_v);
                idx
            };

            let rv_v: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_v)).collect();
            let rv2_v: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_v)).collect();

            #[cfg(feature = "parallel")]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                a.par_iter_mut().zip(bv.par_iter_mut()).zip(rv_v.par_iter())
                    .for_each(|((x, y), r)| { *x += &g_table * r; *y += &f_table * r; });
                (a, bv)
            };
            #[cfg(not(feature = "parallel"))]
            let (c1p_v, c2p_v) = {
                let mut a: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c1_v[i]).collect();
                let mut bv: Vec<RistrettoPoint> = idx_v.iter().map(|&i| c2_v[i]).collect();
                for (j, r) in rv_v.iter().enumerate() { a[j] += &g_table * r; bv[j] += &f_table * r; }
                (a, bv)
            };

            #[cfg(feature = "parallel")]
            let (d1p_v, d2p_v): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
                let (d1s, d2s): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) =
                    d1_v.par_iter().zip(d2_v.par_iter()).enumerate()
                        .map(|(i, (p1, p2))| { let a = alphas_v[i / block_size]; (p1 * a, p2 * a) })
                        .unzip();
                idx_v.par_iter().zip(rv2_v.par_iter())
                    .map(|(&i, r2)| (d1s[i] + &g_table * r2, d2s[i] + &f2_table * r2))
                    .unzip()
            };
            #[cfg(not(feature = "parallel"))]
            let (d1p_v, d2p_v): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) = {
                let (d1s, d2s): (Vec<RistrettoPoint>, Vec<RistrettoPoint>) =
                    d1_v.iter().zip(d2_v.iter()).enumerate()
                        .map(|(i, (p1, p2))| { let a = alphas_v[i / block_size]; (p1 * a, p2 * a) })
                        .unzip();
                idx_v.iter().zip(rv2_v.iter())
                    .map(|(&i, r2)| (d1s[i] + &g_table * r2, d2s[i] + &f2_table * r2))
                    .unzip()
            };

            let c1_v_bytes = batch_compress(&c1_v);
            let c2_v_bytes = batch_compress(&c2_v);
            let d1_v_bytes = batch_compress(&d1_v);
            let d2_v_bytes = batch_compress(&d2_v);
            let c1p_v_bytes = batch_compress(&c1p_v);
            let c2p_v_bytes = batch_compress(&c2p_v);
            let d1p_v_bytes = batch_compress(&d1p_v);
            let d2p_v_bytes = batch_compress(&d2p_v);

            let (inp_v, e_seed_v) = derive_challenge_e(
                &pc_gens, &bp_gens,
                &c1_v_bytes, &c2_v_bytes, &c1p_v_bytes, &c2p_v_bytes,
                Some(&d1_v_bytes), Some(&d2_v_bytes), Some(&d1p_v_bytes), Some(&d2p_v_bytes), Some(&anchor_v_bytes),
                num_blocks, block_size, n_input, circuit_n,
            );
            let mut out_v: Vec<Scalar> = idx_v.iter().map(|&i| inp_v[i]).collect();
            out_v.resize(circuit_n, Scalar::ZERO);
            let rp_v: Scalar = {
                let s = (0..n_input).map(|j| rv_v[j] * inp_v[idx_v[j]]).fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };
            let rp2_v: Scalar = {
                let s = (0..n_input).map(|j| rv2_v[j] * inp_v[idx_v[j]]).fold(Scalar::ZERO, |acc, x| acc + x);
                -s
            };
            let e_v = &inp_v[..n_input];
            let mut pt = Transcript::new(b"MAYA-Shuffle-v1");
            let mut setup_rng = rand::thread_rng();
            let (proof_v, out_com_v) = KShuffleGadget::prove(
                &pc_gens, &bp_gens, &mut pt, &e_seed_v,
                &inp_v, &out_v, &c1p_v, &c2p_v, rp_v, k, d,
                num_blocks, block_size,
                Some(&d1p_v), Some(&d2p_v),
                Some(rp2_v), Some(&alphas_v),
                Some(&d1_v), Some(&d2_v),
                Some(&alpha_pubs_v_c),
                &mut setup_rng,
            )
            .expect("prove for verifier bench failed");


            let c1p_v_c = blob_to_compressed(&c1p_v_bytes);
            let c2p_v_c = blob_to_compressed(&c2p_v_bytes);
            let c1_v_c = blob_to_compressed(&c1_v_bytes);
            let c2_v_c = blob_to_compressed(&c2_v_bytes);
            let d1p_v_c = blob_to_compressed(&d1p_v_bytes);
            let d2p_v_c = blob_to_compressed(&d2p_v_bytes);
            let d1_v_c = blob_to_compressed(&d1_v_bytes);
            let d2_v_c = blob_to_compressed(&d2_v_bytes);

            c.bench_function(&label, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let res = KShuffleGadget::verify(
                        &pc_gens, &bp_gens, &mut t, &e_seed_v, k, d,
                        &proof_v, &inp_v, out_com_v,
                        &c1p_v_c, &c2p_v_c,
                        &c1_v_c, &c2_v_c, e_v,
                        num_blocks, block_size,
                        Some(&d1p_v_c), Some(&d2p_v_c),
                        Some(&d1_v_c), Some(&d2_v_c),
                        Some(&alpha_pubs_v_c),
                    );
                    assert!(res.is_ok(), "verifier bench failed: {:?}", res.err());
                });
            });
        }
         }
        results.push(RunResult {
            n: n_input,
            k,
            d,
            num_blocks,
            block_size,
            total_prover_ms: total_prover_e2e,
            total_verifier_ms: total_verifier_e2e,
            proof_bytes: proof_size,
            proof_gen_ms: t_proof_gen_ms,
            verify_ms: t_verify_ms,
        });
    }

    println!();
    println!("================================================================");
    println!("  All {} configs completed.", configs.len());
    println!("================================================================");

    // SUMMARY TABLE

    let read_criterion_mean_ms = |n: usize, num_blocks: usize, block_size: usize, role: &str| -> Option<f64> {
        let label = if role == "prover" {
            format!("pi5/P/n={}/B={}/b={}", n, num_blocks, block_size)
        } else {
            format!("pi5/V/n={}/B={}/b={}", n, num_blocks, block_size)
        };
        let dir_name = label.replace('/', "_");
        let json_path = format!("target/criterion/{}/new/estimates.json", dir_name);
        let content = match std::fs::read_to_string(&json_path) {
            Ok(c) => c,
            Err(_) => {
                eprintln!("  [criterion] Could not read: {}", json_path);
                return None;
            }
        };
        let mean_key = "\"mean\"";
        let pe_key = "\"point_estimate\":";
        let mean_pos = content.find(mean_key)?;
        let after_mean = &content[mean_pos..];
        let pe_pos = after_mean.find(pe_key)?;
        let val_start = pe_pos + pe_key.len();
        let val_str = &after_mean[val_start..];
        let val_end = val_str.find(|c: char| c == ',' || c == '}' || c == ' ').unwrap_or(val_str.len());
        let ns_value: f64 = match val_str[..val_end].trim().parse() {
            Ok(v) => v,
            Err(_) => {
                eprintln!("  [criterion] Could not parse point_estimate in: {}", json_path);
                return None;
            }
        };
        Some(ns_value / 1_000_000.0)
    };

    let thread_label_summary = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

    let criterion_available = results.iter().any(|r|
        read_criterion_mean_ms(r.n, r.num_blocks, r.block_size, "prover").is_some()
    );

    let averaged_prover = |r: &RunResult| -> f64 {
        match read_criterion_mean_ms(r.n, r.num_blocks, r.block_size, "prover") {
            Some(crit_ms) => crit_ms + (r.total_prover_ms - r.proof_gen_ms),
            None => r.total_prover_ms,
        }
    };
    let averaged_verifier = |r: &RunResult| -> f64 {
        match read_criterion_mean_ms(r.n, r.num_blocks, r.block_size, "verifier") {
            Some(crit_ms) => crit_ms + (r.total_verifier_ms - r.verify_ms),
            None => r.total_verifier_ms,
        }
    };

    if quick_mode {
        if let Some(r) = results.first() {
            let p_ms = averaged_prover(r);
            let v_ms = averaged_verifier(r);
            println!("================================================================");
            println!("  Quick-check result - N={}, B={}, b={}", r.n, r.num_blocks, r.block_size);
            println!();
            println!("  Criterion reports the slope estimate on screen by default (linear");
            println!("  regression of time vs iteration count). The summary table");
            println!("  below uses the mean from target/criterion/*/new/estimates.json,");
            println!("  which is the arithmetic average per-iteration time.");
            println!("  Both differ by ~1%.");
            println!("================================================================");
            println!();
            println!("  Prover (E2E, incl. CRS + disk I/O):   {:>10.2} ms", p_ms);
            println!("  Verifier (E2E, incl. CRS + disk I/O): {:>10.2} ms", v_ms);
            println!(
            "  Proof size:            {:>10} bytes ({:.2} KB)",
            r.proof_bytes,
            r.proof_bytes as f64 / 1024.0
            );            
            println!();
            println!("  Build verification passed.");
            println!("================================================================");
        }
    } else {
        println!("================================================================");
        if criterion_available {
            println!("  Summary - {}", thread_label_summary);
            println!();
            println!("  Criterion reports the slope estimate on screen by default (linear");
            println!("  regression of time vs iteration count). The summary table");
            println!("  below uses the mean from target/criterion/*/new/estimates.json,");
            println!("  which is the arithmetic average per-iteration time.");
            println!("  Both differ by ~1%.");
        } else {
            println!("  Summary - {}", thread_label_summary);
            println!("  Note: Criterion data could not be found in your target/criterion/.");
            println!("  Values below are from a single execution.");
        }
        println!("================================================================");
        println!();

        println!("  {:>10}  {:>4}  {:>8}  {:>6}  {:>4}  {:>14}  {:>14}  {:>12}",
            "N", "k", "B", "b", "d", "Prover (ms)", "Verifier (ms)", "Proof (bytes)");
        println!("  {:->10}  {:->4}  {:->8}  {:->6}  {:->4}  {:->14}  {:->14}  {:->12}",
            "", "", "", "", "", "", "", "");
        for r in &results {
            println!("  {:>10}  {:>4}  {:>8}  {:>6}  {:>4}  {:>14.2}  {:>14.2}  {:>12} ",
                r.n, r.k, r.num_blocks, r.block_size, r.d,
                averaged_prover(r), averaged_verifier(r), r.proof_bytes);
        }
        println!();
    }

}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(SAMPLES)
        .measurement_time(std::time::Duration::from_secs(30));
    targets = custom_benchmark
}


criterion_main!(benches);

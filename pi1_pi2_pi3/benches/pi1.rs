#![allow(dead_code)]
#![allow(unused_imports)]
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
use rand::SeedableRng;

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

// Shuffle Gadget
struct KShuffleGadget;

impl KShuffleGadget {
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
        num_blocks: usize,
        block_size: usize,
        rng: &mut (impl rand::RngCore + rand::CryptoRng),
    ) -> Result<(R1CSProof, CompressedRistretto), R1CSError> {
        let k = input.len();
        let k_original = c1_prime.len();
        if k <= 1 {
            return Err(R1CSError::InputLengthError);
        }

        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());
        transcript.append_message(b"num_blocks", Scalar::from(num_blocks as u64).as_bytes());
        transcript.append_message(b"block_size", Scalar::from(block_size as u64).as_bytes());

        let mut prover = Prover::new(bp_gens, pc_gens, transcript);
        let v_blinding = Scalar::random(rng);
        let (output_commitment, output_vars) = prover.commit_vec(output, v_blinding, k_original);
        let mut cs = prover.finalize_inputs();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, num_blocks, block_size);
        let phase2_sizes = vec![k_original];
        let proof = cs.prove(
            c1_prime, c2_prime, f_gens, r_primes, &phase2_sizes, k_fold, num_rounds,
        )?;
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
        num_blocks: usize,
        block_size: usize,
    ) -> Result<(), R1CSError> {
        let k = input.len();
        transcript.append_message(b"dom-sep", b"ShuffleProof");
        transcript.append_message(b"k", Scalar::from(k as u64).as_bytes());
        transcript.append_message(b"num_blocks", Scalar::from(num_blocks as u64).as_bytes());
        transcript.append_message(b"block_size", Scalar::from(block_size as u64).as_bytes());

        let mut verifier = Verifier::new(bp_gens, pc_gens, transcript);
        let output_vars = verifier.commit_vec(output_commitment, k);
        let mut cs = verifier.finalize_inputs();
        let k_original = c1_prime.len();
        Self::fill_cs(&mut cs, &output_vars, input, k_original, num_blocks, block_size);
        let phase2_sizes = vec![k_original];
        cs.verify(proof, c1_prime, c2_prime, c1_raw, c2_raw, e_challenge, f_gens, &phase2_sizes)
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
    num_blocks: usize,
    block_size: usize,
    n_original: usize,
    n_padded: usize,
) -> Vec<Scalar> {
    let mut ts = Transcript::new(b"FiatShamir-e");
    ts.append_message(b"dom-sep", b"challenge-e-derivation");
    ts.commit_point(b"pk_g", &pc_gens.B.compress());
    ts.commit_point(b"pk_f", &pc_gens.F.compress());
    ts.commit_point(b"ck_h", &pc_gens.B_blinding.compress());
    <Transcript as TranscriptProtocol>::commit_u64(&mut ts, b"ck_n", bp_gens.gens_capacity as u64);
    ts.append_message(b"ck_g_seed", &bp_gens.G_seed);
    ts.append_message(b"ck_h_seed", &bp_gens.H_seed);

    ts.append_message(b"c1",  c1_bytes);
    ts.append_message(b"c2",  c2_bytes);
    ts.append_message(b"c1p", c1p_bytes);
    ts.append_message(b"c2p", c2p_bytes);
    ts.append_message(b"num_blocks", &(num_blocks as u64).to_le_bytes());
    ts.append_message(b"block_size", &(block_size as u64).to_le_bytes());

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

// Benchmark-only deterministic RNG.
// Replace with OsRng or another OS-seeded CSPRNG outside tests/benchmarks.
#[cfg(all(feature = "parallel", not(feature = "production")))]
fn deterministic_rand_scalar(index: usize) -> Scalar {
    const DOMAIN_TAG: u64 = 0xD0_53_BE_4C_1A_27_0E_F1;
    let mut seed = [0u8; 32];
    seed[..8].copy_from_slice(&(index as u64).to_le_bytes());
    seed[8..16].copy_from_slice(&DOMAIN_TAG.to_le_bytes());
    let mut rng = rand::rngs::StdRng::from_seed(seed);
    Scalar::random(&mut rng)
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

fn write_ciphertexts(
    path: &str,
    c1: &[RistrettoPoint],
    c2: &[RistrettoPoint],
    g: &RistrettoPoint,
    f: &RistrettoPoint,
    h: &RistrettoPoint,
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
    w.write_all(f.compress().as_bytes())?;
    w.write_all(h.compress().as_bytes())?;
    w.flush()?;
    let fh = w.into_inner()?;
    fh.sync_all()?;
    Ok(std::fs::metadata(path)?.len() as usize)
}
#[allow(dead_code)]
fn read_ciphertexts(path: &str) -> std::io::Result<(
    Vec<RistrettoPoint>, Vec<RistrettoPoint>,
    RistrettoPoint, RistrettoPoint, RistrettoPoint,
    Vec<u8>, Vec<u8>,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

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
        let mut buf32 = [0u8; 32];
        let mut read_vec = |rdr: &mut BufReader<File>| -> std::io::Result<(Vec<RistrettoPoint>, Vec<u8>)> {
            let mut pts = Vec::with_capacity(n);
            let mut raw = Vec::with_capacity(n * 32);
            for _ in 0..n {
                rdr.read_exact(&mut buf32)?;
                raw.extend_from_slice(&buf32);
                pts.push(
                    CompressedRistretto::from_slice(&buf32)
                        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
                        .decompress()
                        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "decompress failed"))?,
                );
            }
            Ok((pts, raw))
        };
        let (c1, c1_raw) = read_vec(&mut r)?;
        let (c2, c2_raw) = read_vec(&mut r)?;
        (c1, c2, c1_raw, c2_raw)
    };

    let mut buf32 = [0u8; 32];
    let decomp = |b: [u8; 32], label: &'static str| -> std::io::Result<RistrettoPoint> {
        CompressedRistretto::from_slice(&b)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
            .decompress()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("decompress {} failed", label)))
    };
    r.read_exact(&mut buf32)?; let g = decomp(buf32, "g")?;
    r.read_exact(&mut buf32)?; let f = decomp(buf32, "f")?;
    r.read_exact(&mut buf32)?; let h = decomp(buf32, "h")?;
    Ok((c1, c2, g, f, h, c1_raw, c2_raw))
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

#[allow(dead_code)]
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


fn read_ciphertexts_raw(path: &str) -> std::io::Result<(
    Vec<u8>, Vec<u8>,
    RistrettoPoint, RistrettoPoint, RistrettoPoint,
)> {
    let file = File::open(path)?;
    let mut r = BufReader::new(file);
    let mut buf8 = [0u8; 8];
    r.read_exact(&mut buf8)?;
    let n = u64::from_le_bytes(buf8) as usize;

    let mut blob = vec![0u8; 2 * n * 32];
    r.read_exact(&mut blob)?;
    let s = n * 32;
    let c1_raw = blob[..s].to_vec();
    let c2_raw = blob[s..].to_vec();

    let mut buf32 = [0u8; 32];
    let decomp = |b: [u8; 32], label: &'static str| -> std::io::Result<RistrettoPoint> {
        CompressedRistretto::from_slice(&b)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("{}", e)))?
            .decompress()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("decompress {} failed", label)))
    };
    r.read_exact(&mut buf32)?; let g = decomp(buf32, "g")?;
    r.read_exact(&mut buf32)?; let f = decomp(buf32, "f")?;
    r.read_exact(&mut buf32)?; let h = decomp(buf32, "h")?;
    Ok((c1_raw, c2_raw, g, f, h))
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

fn generate_block_permutation(
    num_blocks: usize,
    block_size: usize,
    rng: &mut impl rand::RngCore,
) -> Vec<usize> {
    let n = num_blocks * block_size;
    let mut indices: Vec<usize> = (0..n).collect();
    for beta in 0..num_blocks {
        let start = beta * block_size;
        indices[start..start + block_size].shuffle(rng);
    }
    indices
}

// Main benchmark 
#[allow(unused_variables)]
fn custom_benchmark(c: &mut Criterion) {
    let quick_mode = std::env::var("QUICK")
        .ok()
        .filter(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .is_some();

    // (k_fold (the folding factor), B = num_blocks (nb_voters), b = block_size (nb_candidates))
    let configs: Vec<(usize, usize, usize)> = if quick_mode {
        vec![(4, 100, 20)]
    } else {
        vec![ 
            (4, 1_000,   20),  
            (4, 1_000,   80),  
            (4, 1_000,   320),
            (4, 10_000,  20),  
            (4, 10_000,  80), 
            (4, 100_000,  20), 
            //(4, 10_000,  320),
            // (4, 100_000, 320), 
        ]
    };

    let features = if cfg!(feature = "parallel") { "parallel" } else { "none" };
    println!();
    println!("================================================================");
    println!("  Pi_1 benchmark: single-key, fixed block sizes");
    println!("  Configurations ({} total):", configs.len());
    for (idx, &(_k, nb, bs)) in configs.iter().enumerate() {
        println!("    {:>2}.  N={}  B={}  b={}", idx+1, nb*bs, nb, bs);
    }
    println!("  Features: {}", features);
    println!("================================================================");

    let input_ciph_path   = "./maya_ristretto_pi1_input_ciph.bin";
    let output_bundle_path = "./maya_ristretto_pi1_output_bundle.bin";

    #[allow(dead_code)]
    struct RunResult {
        n: usize, k: usize, d: usize, nb: usize, bs: usize,
        total_prover_ms: f64, total_verifier_ms: f64,
        proof_bytes: usize, proof_gen_ms: f64, verify_ms: f64,
    }
    let mut results: Vec<RunResult> = Vec::new();

    for (i, &(k, num_blocks, block_size)) in configs.iter().enumerate() {
        let n_input = num_blocks * block_size;
        let n_padded = n_input + (k - 1) + 1; //+1 for a safe margin

        let pc_gens = PedersenGens::default();

        let mut rng = rand::thread_rng();
        let g = pc_gens.B;
        let f = pc_gens.F;

        let t_table_start = Instant::now();
        let g_table = RistrettoBasepointTable::create(&g);
        let f_table = RistrettoBasepointTable::create(&f);
        let t_table = t_table_start.elapsed();

        let rem = n_input % k;
        let circuit_n = if rem == 0 { n_input } else { n_input + (k - rem) };
        let mut n_j = circuit_n;
        let mut d = 0usize;
        while n_j > 1 {
            let r = n_j % k;
            let p = if r == 0 { 0 } else { k - r };
            n_j = (n_j + p) / k;
            d += 1;
        }

        let c1_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
        let c2_raw: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();

        let input_file_size = write_ciphertexts(
            input_ciph_path, &c1_raw, &c2_raw, &g, &f, &pc_gens.B_blinding,
        ).expect("write_ciphertexts failed");

        // SINGLE-RUN PROVER

        let t_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let (bp_gens, (c1_bytes, c2_bytes, _g_rd, _f_rd, _h_rd)) = rayon::join(
            || BulletproofGens::new(n_padded, 1),
            || read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed"),
        );
        #[cfg(not(feature = "parallel"))]
        let bp_gens = BulletproofGens::new(n_padded, 1);
        #[cfg(not(feature = "parallel"))]
        let (c1_bytes, c2_bytes, _g_rd, _f_rd, _h_rd) =
            read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed");
        let t_gen = t_gen_start.elapsed();

        let t_decomp_start = Instant::now();
        #[cfg(feature = "parallel")]
        let (c1, c2) = {
            let (r1, r2) = rayon::join(
                || batch_decompress(&c1_bytes).expect("decompress c1 failed"),
                || batch_decompress(&c2_bytes).expect("decompress c2 failed"),
            );
            (r1, r2)
        };
        #[cfg(not(feature = "parallel"))]
        let c1 = batch_decompress(&c1_bytes).expect("decompress c1 failed");
        #[cfg(not(feature = "parallel"))]
        let c2 = batch_decompress(&c2_bytes).expect("decompress c2 failed");
        let t_decomp = t_decomp_start.elapsed();

        let t_shuffle_start = Instant::now();
        let indices = generate_block_permutation(num_blocks, block_size, &mut rng);
        let c1_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c1[i]).collect();
        let c2_prime_init: Vec<RistrettoPoint> = indices.iter().map(|&i| c2[i]).collect();
        let t_shuffle = t_shuffle_start.elapsed();

        let t_rerand_start = Instant::now();
        #[cfg(all(feature = "parallel", not(feature = "production")))]
        let r_values: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
        #[cfg(not(feature = "parallel"))]
        let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

        #[cfg(feature = "parallel")]
        let (c1_prime, c2_prime) = {
            let mut c1p = c1_prime_init;
            let mut c2p = c2_prime_init;
            c1p.par_iter_mut().zip(c2p.par_iter_mut()).zip(r_values.par_iter())
                .for_each(|((a, b), r)| { *a += &g_table * r; *b += &f_table * r; });
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

        let t_e_derive_p_start = Instant::now();
        let c1p_bytes = batch_compress(&c1_prime);
        let c2p_bytes = batch_compress(&c2_prime);
        let input_padded = derive_challenge_e(
            &pc_gens, &bp_gens,
            &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes,
            num_blocks, block_size, n_input, circuit_n,
        );
        let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
        output_padded.resize(circuit_n, Scalar::ZERO);
        let f_gens_vec: Vec<RistrettoPoint> = vec![pc_gens.F];
        let r_prime_single = -(0..n_input)
            .map(|j| r_values[j] * input_padded[indices[j]])
            .fold(Scalar::ZERO, |acc, x| acc + x);
        let r_primes: Vec<Scalar> = vec![r_prime_single];
        let e_original = &input_padded[..n_input];
        let t_e_derive_p = t_e_derive_p_start.elapsed();

        let t_proof_start = Instant::now();
        let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let (proof, out_commitment) = KShuffleGadget::prove(
            &pc_gens, &bp_gens, &mut prover_transcript,
            &input_padded, &output_padded,
            &c1_prime, &c2_prime, &f_gens_vec, &r_primes,
            k, d, num_blocks, block_size, &mut rng,
        ).expect("Proof generation failed");
        let t_proof_gen = t_proof_start.elapsed();

        let t_write_start = Instant::now();
        let output_file_size = write_proof_bundle(
            output_bundle_path, &proof, &out_commitment, &c1p_bytes, &c2p_bytes,
        ).expect("write_proof_bundle failed");
        let t_file_write = t_write_start.elapsed();

        let proof_size: usize = proof.to_bytes().len();
        
        // Let the CPU cool down before doing the Verifier
        std::thread::sleep(std::time::Duration::from_secs(30));


        // SINGLE-RUN VERIFIER

        let t_v_gen_start = Instant::now();
        #[cfg(feature = "parallel")]
        let ((v_pc_gens, v_bp_gens), ((proof_r, out_commitment_r, c1p_r_bytes, c2p_r_bytes), (c1_orig_bytes, c2_orig_bytes, _g_v, _f_v, _h_v))) =
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
        let (proof_r, out_commitment_r, c1p_r_bytes, c2p_r_bytes) =
            read_proof_bundle_raw(output_bundle_path).expect("read_proof_bundle_raw failed");
        #[cfg(not(feature = "parallel"))]
        let (c1_orig_bytes, c2_orig_bytes, _g_v, _f_v, _h_v) =
            read_ciphertexts_raw(input_ciph_path).expect("read_ciphertexts_raw failed");
        let t_v_gen = t_v_gen_start.elapsed();


        let t_e_start = Instant::now();
        let input_padded_r = derive_challenge_e(
            &v_pc_gens, &v_bp_gens,
            &c1_orig_bytes, &c2_orig_bytes,
            &c1p_r_bytes, &c2p_r_bytes,
            num_blocks, block_size, n_input, circuit_n,
        );
        let t_e_derive = t_e_start.elapsed();

        let e_original_r = &input_padded_r[..n_input];
      
        let c1_prime_c = blob_to_compressed(&c1p_r_bytes);
        let c2_prime_c = blob_to_compressed(&c2p_r_bytes);
        let c1_raw_c = blob_to_compressed(&c1_orig_bytes);
        let c2_raw_c = blob_to_compressed(&c2_orig_bytes);
        let f_gens_v: Vec<RistrettoPoint> = vec![v_pc_gens.F];
        let f_gens_v_c = compress_all_par(&f_gens_v);
        let t_verify_start = Instant::now();
        let mut verifier_transcript = Transcript::new(b"MAYA-Shuffle-v1");
        let result = KShuffleGadget::verify(
            &v_pc_gens,
            &v_bp_gens,
            &mut verifier_transcript,
            &proof_r,
            &input_padded_r,
            out_commitment_r,
            &c1_prime_c,
            &c2_prime_c,
            &c1_raw_c,
            &c2_raw_c,
            e_original_r,
            &f_gens_v_c,
            num_blocks,
            block_size,
        );
        assert!(result.is_ok(),
            "Verification failed N={}/k={}/d={}: {:?}", n_input, k, d, result.err());
        let t_verify = t_verify_start.elapsed();

        let ms = |dur: std::time::Duration| dur.as_secs_f64() * 1000.0;
        let t_gen_ms        = ms(t_gen);
        let t_decomp_ms     = ms(t_decomp);
        let t_table_ms      = ms(t_table);
        let t_shuffle_ms    = ms(t_shuffle);
        let t_rerand_ms     = ms(t_rerand);
        let t_e_derive_p_ms = ms(t_e_derive_p);
        let t_proof_gen_ms  = ms(t_proof_gen);
        let t_file_write_ms = ms(t_file_write);
        let t_v_gen_ms      = ms(t_v_gen);
        let t_e_derive_ms   = ms(t_e_derive);
        let t_verify_ms     = ms(t_verify);
        let total_prover    = t_gen_ms + t_decomp_ms + t_table_ms + t_shuffle_ms + t_rerand_ms
                              + t_e_derive_p_ms + t_proof_gen_ms;
        let file_io         = t_file_write_ms;
        let total_prover_e2e = total_prover + file_io;
        let total_verifier  = t_v_gen_ms + t_e_derive_ms + t_verify_ms;
        let total_verifier_e2e = total_verifier;
        let thread_label    = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };

        println!();
        println!("================================================================");
        println!("  Config [{}/{}]: N={}  B={}  b={}  ({})",
            i+1, configs.len(), n_input, num_blocks, block_size, thread_label);
        println!("================================================================");
        println!("  PROVER:");
        //println!("    Folding depth:           d={}  k_fold={}", d, k);
        println!("    CRS+DiskRead (wall):     {:>14.2} ms", t_gen_ms);
        println!("    Fixed-base table:        {:>14.2} ms", t_table_ms);
        println!("    Batch decompress C1+C2:  {:>14.2} ms", t_decomp_ms);
        println!("    Permutation:             {:>14.2} ms", t_shuffle_ms);
        println!("    Rerandomization:         {:>14.2} ms", t_rerand_ms);
        println!("    Challenge e derivation:  {:>14.2} ms", t_e_derive_p_ms);
        println!("    Proof generation (*):    {:>14.2} ms", t_proof_gen_ms);
        println!("    File I/O (write only):   {:>14.2} ms", file_io);
        println!("    ─────────────────────────────────────────────────");
        println!("    Total E2E (incl. I/O):   {:>14.2} ms", total_prover_e2e);
        println!("  VERIFIER:");
        println!("    CRS+DiskRead (wall time):{:>14.2} ms", t_v_gen_ms);
        println!("    Challenge e derivation:  {:>14.2} ms", t_e_derive_ms);
        println!("    Proof verification (*):  {:>14.2} ms", t_verify_ms);
        println!("    ────────────────────────────────────────────────");
        println!("    Total E2E:               {:>14.2} ms", total_verifier_e2e);
        println!("  Verification: PASSED");
        println!("  Proof size: {} bytes ({:.2} KB)", proof_size, proof_size as f64 / 1024.0);
        println!("  Input file: {} bytes  Output bundle: {} bytes", input_file_size, output_file_size);

        if CRITERION_ENABLED {
            // CRITERION: Prover
            let label_p = format!("pi1/P/n={}/B={}/b={}", n_input, num_blocks, block_size);
            let mut rng_b = rand::thread_rng();
            let c1_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let c2_b: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_b)).collect();
            let idx_b = generate_block_permutation(num_blocks, block_size, &mut rng_b);
            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_b: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_b)).collect();
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
            let c1_b_bytes = batch_compress(&c1_b);
            let c2_b_bytes = batch_compress(&c2_b);
            let c1p_b_bytes = batch_compress(&c1p_b);
            let c2p_b_bytes = batch_compress(&c2p_b);
            let inp_b = derive_challenge_e(&pc_gens, &bp_gens,
                &c1_b_bytes, &c2_b_bytes, &c1p_b_bytes, &c2p_b_bytes,
                num_blocks, block_size, n_input, circuit_n);
            let mut out_b: Vec<Scalar> = idx_b.iter().map(|&i| inp_b[i]).collect();
            out_b.resize(circuit_n, Scalar::ZERO);
            let f_gens_b: Vec<RistrettoPoint> = vec![pc_gens.F];
            let rp_b: Vec<Scalar> = vec![-(0..n_input)
                .map(|j| rv_b[j] * inp_b[idx_b[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x)];

            c.bench_function(&label_p, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let mut bench_rng = rand::thread_rng();
                    KShuffleGadget::prove(&pc_gens, &bp_gens, &mut t,
                        &inp_b, &out_b, &c1p_b, &c2p_b, &f_gens_b, &rp_b,
                        k, d, num_blocks, block_size, &mut bench_rng,
                    ).expect("prover bench failed");
                });
            });

            // CRITERION: Verifier
            let label_v = format!("pi1/V/n={}/B={}/b={}", n_input, num_blocks, block_size);
            let mut rng_v = rand::thread_rng();
            let c1_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let c2_v: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng_v)).collect();
            let idx_v = generate_block_permutation(num_blocks, block_size, &mut rng_v);
            #[cfg(all(feature = "parallel", not(feature = "production")))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|j| deterministic_rand_scalar(j)).collect();
            #[cfg(not(feature = "parallel"))]
            let rv_v: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng_v)).collect();
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
            let c1_v_bytes = batch_compress(&c1_v);
            let c2_v_bytes = batch_compress(&c2_v);
            let c1p_v_bytes = batch_compress(&c1p_v);
            let c2p_v_bytes = batch_compress(&c2p_v);
            let inp_v = derive_challenge_e(&pc_gens, &bp_gens,
                &c1_v_bytes, &c2_v_bytes, &c1p_v_bytes, &c2p_v_bytes,
                num_blocks, block_size, n_input, circuit_n);
            let mut out_v: Vec<Scalar> = idx_v.iter().map(|&i| inp_v[i]).collect();
            out_v.resize(circuit_n, Scalar::ZERO);
            let f_gens_v2: Vec<RistrettoPoint> = vec![pc_gens.F];
            let f_gens_v2_c = compress_all_par(&f_gens_v2);
            let rp_v: Vec<Scalar> = vec![-(0..n_input)
                .map(|j| rv_v[j] * inp_v[idx_v[j]])
                .fold(Scalar::ZERO, |acc, x| acc + x)];
            let mut pt = Transcript::new(b"MAYA-Shuffle-v1");
            let mut setup_rng = rand::thread_rng();
            let (proof_v, out_com_v) = KShuffleGadget::prove(
                &pc_gens, &bp_gens, &mut pt,
                &inp_v, &out_v, &c1p_v, &c2p_v, &f_gens_v2, &rp_v,
                k, d, num_blocks, block_size, &mut setup_rng,
            ).expect("prove for verifier bench failed");
            let e_v = &inp_v[..n_input];
            
            let c1p_v_c = blob_to_compressed(&c1p_v_bytes);
            let c2p_v_c = blob_to_compressed(&c2p_v_bytes);
            let c1_v_c = blob_to_compressed(&c1_v_bytes);
            let c2_v_c = blob_to_compressed(&c2_v_bytes);
            c.bench_function(&label_v, |b| {
                b.iter(|| {
                    let mut t = Transcript::new(b"MAYA-Shuffle-v1");
                    let res = KShuffleGadget::verify(
                        &pc_gens, &bp_gens, &mut t,
                        &proof_v, &inp_v, out_com_v,
                        &c1p_v_c, &c2p_v_c, &c1_v_c, &c2_v_c, e_v,
                        &f_gens_v2_c, num_blocks, block_size,
                    );
                    assert!(res.is_ok(), "verifier bench failed: {:?}", res.err());
                });
            });
        }

        results.push(RunResult {
            n: n_input, k, d, nb: num_blocks, bs: block_size,
            total_prover_ms: total_prover_e2e, total_verifier_ms: total_verifier_e2e,
            proof_bytes: proof_size, proof_gen_ms: t_proof_gen_ms, verify_ms: t_verify_ms,
        });
    }

    let thread_label_summary = if cfg!(feature = "parallel") { "multi-threaded" } else { "single-threaded" };
    let read_criterion_mean_ms = |n: usize, _k: usize, nb: usize, bs: usize, role: &str| -> Option<f64> {
        let json_path = format!(
            "target/criterion/pi1_{}_n={}_B={}_b={}/new/estimates.json",
            role, n, nb, bs
        );
        let content = std::fs::read_to_string(&json_path).ok()?;
        let mean_pos = content.find("\"mean\"")?;
        let after_mean = &content[mean_pos..];
        let pe_pos = after_mean.find("\"point_estimate\":")?;
        let val_str = &after_mean[pe_pos + "\"point_estimate\":".len()..];
        let val_end = val_str.find(|c: char| c == ',' || c == '}' || c == ' ').unwrap_or(val_str.len());
        let ns: f64 = val_str[..val_end].trim().parse().ok()?;
        Some(ns / 1_000_000.0)
    };

    let criterion_available = results.iter().any(|r|
        read_criterion_mean_ms(r.n, r.k, r.nb, r.bs, "P").is_some()
    );

    println!();
    println!("================================================================");
    if criterion_available {
        println!("  Summary - {} (Criterion means)", thread_label_summary);
    } else {
        println!("  Summary - {}", thread_label_summary);
    }
    println!("================================================================");
    println!("  {:>10}  {:>7}  {:>5}  {:>14}  {:>14}  {:>12}",
        "N", "B", "b", "Prover (ms)", "Verifier (ms)", "Proof (bytes)");
    println!("  {:->10}  {:->7}  {:->5}  {:->14}  {:->14}  {:->12}",
        "", "", "", "", "", "");
    for r in &results {
        let avg_p = read_criterion_mean_ms(r.n, r.k, r.nb, r.bs, "P")
            .map(|crit| crit + (r.total_prover_ms - r.proof_gen_ms))
            .unwrap_or(r.total_prover_ms);
        let avg_v = read_criterion_mean_ms(r.n, r.k, r.nb, r.bs, "V")
            .map(|crit| crit + (r.total_verifier_ms - r.verify_ms))
            .unwrap_or(r.total_verifier_ms);
        println!("  {:>10}  {:>7}  {:>5}  {:>14.2}  {:>14.2}  {:>12}",
            r.n, r.nb, r.bs, avg_p, avg_v, r.proof_bytes);
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

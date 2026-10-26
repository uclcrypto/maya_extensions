// Integration tests for Pi_3: multi-key, per-key permutations.
include!("../benches/pi3.rs");

const K_FOLD: usize = 4;

// Two keys of 6 ciphertexts each
fn p1_blocks() -> Vec<usize> {
    vec![3, 3, 3, 3]
}
fn p2_groups() -> Vec<usize> {
    vec![6, 6]
}

struct Instance {
    pc_gens: PedersenGens,
    bp_gens: BulletproofGens,
    proof: R1CSProof,
    out_commitment: CompressedRistretto,
    input_padded: Vec<Scalar>,
    e_seed: [u8; 32],
    c1_prime_c: Vec<CompressedRistretto>,
    c2_prime_c: Vec<CompressedRistretto>,
    c1_raw_c: Vec<CompressedRistretto>,
    c2_raw_c: Vec<CompressedRistretto>,
    f_gens_c: Vec<CompressedRistretto>,
    n_input: usize,
    circuit_n: usize,
    d: usize,
}

fn fold_rounds(circuit_n: usize, k: usize) -> usize {
    let mut n_j = circuit_n;
    let mut d = 0usize;
    while n_j > 1 {
        let r = n_j % k;
        n_j = (n_j + if r == 0 { 0 } else { k - r }) / k;
        d += 1;
    }
    d
}

fn run_prover(honest: bool) -> Instance {
    let p1 = p1_blocks();
    let p2 = p2_groups();
    let n_input: usize = p2.iter().sum();
    assert_eq!(p1.iter().sum::<usize>(), n_input);
    let n_padded = n_input + (K_FOLD - 1) + 1;
    let rem = n_input % K_FOLD;
    let circuit_n = if rem == 0 { n_input } else { n_input + (K_FOLD - rem) };
    let d = fold_rounds(circuit_n, K_FOLD);

    let mut rng = rand::thread_rng();
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(n_padded, 1);
    let f_gens: Vec<RistrettoPoint> =
        (0..p2.len()).map(|_| RistrettoPoint::random(&mut rng)).collect();

    let c1: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let c2: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();

    let indices = generate_hetero_block_permutation(&p1, &mut rng);
    let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();

    let mut elem_block: Vec<usize> = Vec::with_capacity(n_input);
    for (ell, &gs) in p2.iter().enumerate() {
        for _ in 0..gs {
            elem_block.push(ell);
        }
    }

    let g_table = RistrettoBasepointTable::create(&pc_gens.B);
    let f_tables: Vec<RistrettoBasepointTable> =
        f_gens.iter().map(|f| RistrettoBasepointTable::create(f)).collect();
    let c1_prime: Vec<RistrettoPoint> = (0..n_input)
        .map(|j| c1[indices[j]] + &g_table * &r_values[j])
        .collect();
    let c2_prime: Vec<RistrettoPoint> = (0..n_input)
        .map(|j| c2[indices[j]] + &f_tables[elem_block[j]] * &r_values[j])
        .collect();

    let c1_bytes = batch_compress(&c1);
    let c2_bytes = batch_compress(&c2);
    let c1p_bytes = batch_compress(&c1_prime);
    let c2p_bytes = batch_compress(&c2_prime);

    let (input_padded, e_seed) = derive_challenge_e(
        &pc_gens, &bp_gens,
        &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes,
        &f_gens, &p1, &p2, n_input, circuit_n,
    );

    let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
    if !honest {
        output_padded[1] = output_padded[0];
    }
    output_padded.resize(circuit_n, Scalar::ZERO);

    let r_primes: Vec<Scalar> = {
        let mut off = 0usize;
        p2.iter()
            .map(|&gs| {
                let s = (off..off + gs)
                    .map(|j| r_values[j] * input_padded[indices[j]])
                    .fold(Scalar::ZERO, |acc, x| acc + x);
                off += gs;
                -s
            })
            .collect()
    };

    let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1-mk");
    let (proof, out_commitment) = KShuffleGadget::prove(
        &pc_gens, &bp_gens, &mut prover_transcript, &e_seed,
        &input_padded, &output_padded,
        &c1_prime, &c2_prime, &f_gens, &r_primes,
        K_FOLD, d, &p1, &p2, &mut rng,
    ).expect("proof generation failed");

    Instance {
        pc_gens, bp_gens, proof, out_commitment, input_padded, e_seed,
        c1_prime_c: blob_to_compressed(&c1p_bytes),
        c2_prime_c: blob_to_compressed(&c2p_bytes),
        c1_raw_c: blob_to_compressed(&c1_bytes),
        c2_raw_c: blob_to_compressed(&c2_bytes),
        f_gens_c: compress_all_par(&f_gens),
        n_input, circuit_n, d,
    }
}

fn verify_with(
    inst: &Instance,
    proof: &R1CSProof,
    e_seed: &[u8; 32],
    c1_raw: &[CompressedRistretto],
    k_fold: usize,
    num_rounds: usize,
    p1: &[usize],
    p2: &[usize],
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1-mk");
    KShuffleGadget::verify(
        &inst.pc_gens, &inst.bp_gens, &mut transcript, e_seed,
        proof, &inst.input_padded, inst.out_commitment,
        &inst.c1_prime_c, &inst.c2_prime_c,
        c1_raw, &inst.c2_raw_c,
        &inst.input_padded[..inst.n_input],
        &inst.f_gens_c, k_fold, num_rounds, p1, p2,
    )
}

fn verify_honest(inst: &Instance) -> Result<(), R1CSError> {
    verify_with(
        inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c,
        K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
    )
}

#[test]
fn honest_proof_verifies() {
    let inst = run_prover(true);
    assert_eq!(inst.n_input, 12);
    assert_eq!(inst.circuit_n, 12);
    assert_eq!(inst.d, 2);
    assert!(verify_honest(&inst).is_ok(), "{:?}", verify_honest(&inst).err());
}

#[test]
fn proof_survives_a_byte_round_trip() {
    let inst = run_prover(true);
    let bytes = inst.proof.to_bytes();
    let reparsed = R1CSProof::from_bytes(&bytes).expect("round trip");
    assert_eq!(reparsed.to_bytes(), bytes);
    assert!(verify_with(
        &inst, &reparsed, &inst.e_seed, &inst.c1_raw_c,
        K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
    ).is_ok());
}

#[test]
fn tampered_proofs_are_rejected() {
    let inst = run_prover(true);
    let bytes = inst.proof.to_bytes();
    for pos in (0..bytes.len()).step_by(64) {
        let mut bad = bytes.clone();
        bad[pos] ^= 1;
        let rejected = match R1CSProof::from_bytes(&bad) {
            Err(_) => true,
            Ok(p) => verify_with(
                &inst, &p, &inst.e_seed, &inst.c1_raw_c,
                K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
            ).is_err(),
        };
        assert!(rejected, "a proof with byte {} flipped verified", pos);
    }
}

#[test]
fn malformed_proof_bytes_are_rejected() {
    let inst = run_prover(true);
    let bytes = inst.proof.to_bytes();

    for cut in [0usize, 1, 31, 32, 95, 200].iter() {
        if *cut < bytes.len() {
            assert!(R1CSProof::from_bytes(&bytes[..*cut]).is_err());
        }
    }
    let mut longer = bytes.clone();
    longer.extend_from_slice(&[0u8; 32]);
    assert!(R1CSProof::from_bytes(&longer).is_err());

    for claim in [u64::max_value(), 1u64 << 60, 1u64 << 40].iter() {
        for offset in 0..(bytes.len().min(1024) / 8) {
            let mut bad = bytes.clone();
            bad[offset * 8..offset * 8 + 8].copy_from_slice(&claim.to_le_bytes());
            let _ = R1CSProof::from_bytes(&bad);
        }
    }
    assert!(R1CSProof::from_bytes(&[]).is_err());
    assert!(R1CSProof::from_bytes(&vec![0u8; 4096]).is_err());
    assert!(R1CSProof::from_bytes(&vec![0xffu8; 4096]).is_err());
}

#[test]
fn the_statement_is_bound_to_the_transcript() {
    let inst = run_prover(true);

    let mut other_seed = inst.e_seed;
    other_seed[0] ^= 1;
    assert!(verify_with(
        &inst, &inst.proof, &other_seed, &inst.c1_raw_c,
        K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
    ).is_err(), "a proof verified against a different e_seed");

    let mut other_c1 = inst.c1_raw_c.clone();
    other_c1.swap(0, 1);
    assert!(verify_with(
        &inst, &inst.proof, &inst.e_seed, &other_c1,
        K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
    ).is_err(), "a proof verified against a different input list");
}

#[test]
fn the_folding_parameters_are_pinned() {
    let inst = run_prover(true);
    for &(k_fold, rounds) in [
        (K_FOLD + 1, inst.d), (K_FOLD - 1, inst.d), (1, inst.d), (0, inst.d),
        (K_FOLD, inst.d + 1), (K_FOLD, inst.d - 1), (K_FOLD, 0),
    ].iter() {
        let res = verify_with(
            &inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c,
            k_fold, rounds, &p1_blocks(), &p2_groups(),
        );
        assert!(res.is_err(), "k_fold={} rounds={} was accepted", k_fold, rounds);
    }
}

#[test]
fn the_two_block_structures_are_bound() {
    let inst = run_prover(true);
    // P1: the permutation blocks
    for alt in [vec![2usize, 4, 3, 3], vec![6, 6], vec![12]].iter() {
        assert!(verify_with(
            &inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c,
            K_FOLD, inst.d, alt, &p2_groups(),
        ).is_err(), "P1 blocks {:?} were accepted", alt);
    }
    // P2: the per-key groups
    for alt in [vec![4usize, 8], vec![8, 4], vec![5, 7]].iter() {
        assert!(verify_with(
            &inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c,
            K_FOLD, inst.d, &p1_blocks(), alt,
        ).is_err(), "P2 groups {:?} were accepted", alt);
    }
}

#[test]
fn a_non_permutation_is_rejected() {
    let inst = run_prover(false);
    assert!(verify_honest(&inst).is_err(), "a non-permutation verified");
}

fn verify_lists(
    inst: &Instance,
    c1_prime: &[CompressedRistretto],
    c2_prime: &[CompressedRistretto],
    c1_raw: &[CompressedRistretto],
    c2_raw: &[CompressedRistretto],
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1-mk");
    KShuffleGadget::verify(
        &inst.pc_gens, &inst.bp_gens, &mut transcript, &inst.e_seed,
        &inst.proof, &inst.input_padded, inst.out_commitment,
        c1_prime, c2_prime, c1_raw, c2_raw,
        &inst.input_padded[..inst.n_input],
        &inst.f_gens_c, K_FOLD, inst.d, &p1_blocks(), &p2_groups(),
    )
}


#[test]
fn malformed_statements_are_rejected() {
    let inst = run_prover(true);

    let mut doubled = inst.c1_prime_c.clone();
    doubled.extend(inst.c1_prime_c.iter().cloned());
    assert!(verify_lists(&inst, &doubled, &doubled, &inst.c1_raw_c, &inst.c2_raw_c).is_err());

    assert!(verify_lists(
        &inst, &inst.c1_prime_c, &inst.c2_prime_c[1..], &inst.c1_raw_c, &inst.c2_raw_c,
    ).is_err());
    assert!(verify_lists(
        &inst, &inst.c1_prime_c, &inst.c2_prime_c, &inst.c1_raw_c[1..], &inst.c2_raw_c,
    ).is_err());
    assert!(verify_lists(
        &inst, &inst.c1_prime_c, &inst.c2_prime_c, &inst.c1_raw_c, &inst.c2_raw_c[1..],
    ).is_err());
    assert!(verify_lists(&inst, &[], &[], &[], &[]).is_err());
}

#[test]
#[ignore]
fn statement_binding_cost() {
    let seed = [7u8; 32];
    let p1: Vec<usize> = (0..500).map(|i| 2 + i % 5).collect();
    let p2: Vec<usize> = vec![p1.iter().sum::<usize>() / 2; 2];
    let reps = 20_000;
    let start = Instant::now();
    for _ in 0..reps {
        let mut t = Transcript::new(b"MAYA-Shuffle-v1-mk");
        KShuffleGadget::bind_statement(&mut t, 1 << 20, &seed, 1_000_000, 4, 10, &p1, &p2);
    }
    println!();
    println!(
        "statement binding ({} P1 blocks, {} keys): {:.3} us per proof",
        p1.len(), p2.len(),
        start.elapsed().as_secs_f64() * 1e6 / reps as f64
    );
}

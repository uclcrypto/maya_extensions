// Integration tests for Pi_2: single key, variable group sizes.
include!("../benches/pi2.rs");

const K_FOLD: usize = 4;

fn block_sizes() -> Vec<usize> {
    vec![3, 2, 4, 2]
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
    let bs = block_sizes();
    let n_input: usize = bs.iter().sum();
    let n_padded = n_input + (K_FOLD - 1) + 1;
    let rem = n_input % K_FOLD;
    let circuit_n = if rem == 0 { n_input } else { n_input + (K_FOLD - rem) };
    let d = fold_rounds(circuit_n, K_FOLD);

    let mut rng = rand::thread_rng();
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(n_padded, 1);

    let c1: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();
    let c2: Vec<RistrettoPoint> = (0..n_input).map(|_| RistrettoPoint::random(&mut rng)).collect();

    let indices = generate_hetero_block_permutation(&bs, &mut rng);
    let r_values: Vec<Scalar> = (0..n_input).map(|_| Scalar::random(&mut rng)).collect();
    let g_table = RistrettoBasepointTable::create(&pc_gens.B);
    let f_table = RistrettoBasepointTable::create(&pc_gens.F);
    let c1_prime: Vec<RistrettoPoint> = (0..n_input)
        .map(|j| c1[indices[j]] + &g_table * &r_values[j])
        .collect();
    let c2_prime: Vec<RistrettoPoint> = (0..n_input)
        .map(|j| c2[indices[j]] + &f_table * &r_values[j])
        .collect();

    let c1_bytes = batch_compress(&c1);
    let c2_bytes = batch_compress(&c2);
    let c1p_bytes = batch_compress(&c1_prime);
    let c2p_bytes = batch_compress(&c2_prime);

    let (input_padded, e_seed) = derive_challenge_e(
        &pc_gens, &bp_gens,
        &c1_bytes, &c2_bytes, &c1p_bytes, &c2p_bytes,
        &bs, n_input, circuit_n,
    );

    let mut output_padded: Vec<Scalar> = indices.iter().map(|&i| input_padded[i]).collect();
    if !honest {
        output_padded[1] = output_padded[0];
    }
    output_padded.resize(circuit_n, Scalar::ZERO);

    let f_gens_vec: Vec<RistrettoPoint> = vec![pc_gens.F];
    let r_prime_single = -(0..n_input)
        .map(|j| r_values[j] * input_padded[indices[j]])
        .fold(Scalar::ZERO, |acc, x| acc + x);
    let r_primes: Vec<Scalar> = vec![r_prime_single];

    let mut prover_transcript = Transcript::new(b"MAYA-Shuffle-v1");
    let (proof, out_commitment) = KShuffleGadget::prove(
        &pc_gens, &bp_gens, &mut prover_transcript, &e_seed,
        &input_padded, &output_padded,
        &c1_prime, &c2_prime, &f_gens_vec, &r_primes,
        K_FOLD, d, &bs, &mut rng,
    ).expect("proof generation failed");

    Instance {
        pc_gens, bp_gens, proof, out_commitment, input_padded, e_seed,
        c1_prime_c: blob_to_compressed(&c1p_bytes),
        c2_prime_c: blob_to_compressed(&c2p_bytes),
        c1_raw_c: blob_to_compressed(&c1_bytes),
        c2_raw_c: blob_to_compressed(&c2_bytes),
        f_gens_c: compress_all_par(&f_gens_vec),
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
    bs: &[usize],
) -> Result<(), R1CSError> {
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1");
    KShuffleGadget::verify(
        &inst.pc_gens, &inst.bp_gens, &mut transcript, e_seed,
        proof, &inst.input_padded, inst.out_commitment,
        &inst.c1_prime_c, &inst.c2_prime_c,
        c1_raw, &inst.c2_raw_c,
        &inst.input_padded[..inst.n_input],
        &inst.f_gens_c, k_fold, num_rounds, bs,
    )
}

fn verify_honest(inst: &Instance) -> Result<(), R1CSError> {
    let bs = block_sizes();
    verify_with(inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c, K_FOLD, inst.d, &bs)
}

#[test]
fn honest_proof_verifies() {
    let inst = run_prover(true);
    assert_eq!(inst.n_input, 11);
    assert_eq!(inst.circuit_n, 12);
    assert_eq!(inst.d, 2);
    assert!(verify_honest(&inst).is_ok(), "{:?}", verify_honest(&inst).err());
}

#[test]
fn proof_survives_a_byte_round_trip() {
    let inst = run_prover(true);
    let bs = block_sizes();
    let bytes = inst.proof.to_bytes();
    let reparsed = R1CSProof::from_bytes(&bytes).expect("round trip");
    assert_eq!(reparsed.to_bytes(), bytes);
    assert!(verify_with(&inst, &reparsed, &inst.e_seed, &inst.c1_raw_c, K_FOLD, inst.d, &bs).is_ok());
}

#[test]
fn tampered_proofs_are_rejected() {
    let inst = run_prover(true);
    let bs = block_sizes();
    let bytes = inst.proof.to_bytes();
    for pos in (0..bytes.len()).step_by(64) {
        let mut bad = bytes.clone();
        bad[pos] ^= 1;
        let rejected = match R1CSProof::from_bytes(&bad) {
            Err(_) => true,
            Ok(p) => verify_with(&inst, &p, &inst.e_seed, &inst.c1_raw_c, K_FOLD, inst.d, &bs).is_err(),
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
    let bs = block_sizes();

    let mut other_seed = inst.e_seed;
    other_seed[0] ^= 1;
    assert!(verify_with(&inst, &inst.proof, &other_seed, &inst.c1_raw_c, K_FOLD, inst.d, &bs).is_err(),
        "a proof verified against a different e_seed");

    let mut other_c1 = inst.c1_raw_c.clone();
    other_c1.swap(0, 1);
    assert!(verify_with(&inst, &inst.proof, &inst.e_seed, &other_c1, K_FOLD, inst.d, &bs).is_err(),
        "a proof verified against a different input list");
}

#[test]
fn the_folding_parameters_are_pinned() {
    let inst = run_prover(true);
    let bs = block_sizes();
    for &(k_fold, rounds) in [
        (K_FOLD + 1, inst.d), (K_FOLD - 1, inst.d), (1, inst.d), (0, inst.d),
        (K_FOLD, inst.d + 1), (K_FOLD, inst.d - 1), (K_FOLD, 0),
    ].iter() {
        let res = verify_with(&inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c, k_fold, rounds, &bs);
        assert!(res.is_err(), "k_fold={} rounds={} was accepted", k_fold, rounds);
    }
}

#[test]
fn the_group_sizes_are_bound() {
    let inst = run_prover(true);
    for alt in [
        vec![2usize, 3, 4, 2],
        vec![3, 2, 2, 4],
        vec![3, 4, 2, 2],
        vec![11],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ].iter() {
        assert!(
            verify_with(&inst, &inst.proof, &inst.e_seed, &inst.c1_raw_c, K_FOLD, inst.d, alt).is_err(),
            "group sizes {:?} were accepted for a {:?} proof", alt, block_sizes()
        );
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
    let bs = block_sizes();
    let mut transcript = Transcript::new(b"MAYA-Shuffle-v1");
    KShuffleGadget::verify(
        &inst.pc_gens, &inst.bp_gens, &mut transcript, &inst.e_seed,
        &inst.proof, &inst.input_padded, inst.out_commitment,
        c1_prime, c2_prime, c1_raw, c2_raw,
        &inst.input_padded[..inst.n_input],
        &inst.f_gens_c, K_FOLD, inst.d, &bs,
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
    let groups: Vec<usize> = (0..50).map(|i| 10 + i % 7).collect();
    let reps = 20_000;
    let start = Instant::now();
    for _ in 0..reps {
        let mut t = Transcript::new(b"MAYA-Shuffle-v1");
        KShuffleGadget::bind_statement(&mut t, 1 << 20, &seed, 1_000_000, 4, 10, &groups);
    }
    println!();
    println!(
        "statement binding ({} groups): {:.3} us per proof",
        groups.len(),
        start.elapsed().as_secs_f64() * 1e6 / reps as f64
    );
}

# MAYAsk: Swiss-Knife Extensions to MAYA

> **Research code.** This is a research prototypeonly -- for benchmarking and experimentation. Not audited, no correctness or security guarantees. Do NOT use in production or any deployed system.

This repository contains a Rust implementation and benchmarks of the MAYA extensions (Pi_1 - Pi_6) built on top of the MAYA shuffle argument (`O(log n)` proof size, Ristretto255).
 It contains
four self-contained Cargo crates, each an instantiation of the same MAYA R1CS
prover/verifier core specialized to one family of protocols. The repository accompanies the paper accepted at NordSec 2026 https://nordsec2026.dk/#home.

More information about MAYA is available on  https://thaodoanvan.github.io/maya_website/.

| Protocol | Description                                                                    | Crate                    | Benchmark        | Tests            |
|----------|--------------------------------------------------------------------------------|--------------------------|------------------|------------------|
| **Pi_1** | Uniform blocks, single key                                                     | `pi1_pi2_pi3`            | `benches/pi1.rs` | `tests/pi1.rs`   |
| **Pi_2** | Heterogeneous blocks, single key                                               | `pi1_pi2_pi3`            | `benches/pi2.rs` | `tests/pi2.rs`   |
| **Pi_3** | Multiple keys, each key with its own block structure                           | `pi1_pi2_pi3`            | `benches/pi3.rs` | `tests/pi3.rs`   |
| **Pi_4** | Decryption mixnet (one mixer): shuffle-and-partial-decryption                  | `pi4_dec_mix`            | `benches/pi4.rs` | `tests/pi4.rs`   |
| **Pi_5** | Shuffle-and-exponentiate (`DbleMixExp`), one secret exponent per voter (block) | `pi5_dbl_mix_exp`        | `benches/pi5.rs` | `tests/pi5.rs`   |
| **Pi_6** | Shuffle-and-exponentiate (`DbleMixExp`), one secret exponent for all voters    | `pi6_dbl_mix_exp_single` | `benches/pi6.rs` | `tests/pi6.rs`   |


Pi_5 and Pi_6 are two variants of `DbleMixExp`. Both shuffle pairs of ciphertexts under two keys with one block permutation,
re-randomize both, and raise the second-key ciphertexts to a secret exponent
anchored in a public value `K = g^alpha`. They differ only in how many exponents
there are. For Pi_5, voter (block) `beta` has its own exponent `alpha_beta` and anchor
  `K_beta`. For Pi_6, a single exponent `alpha` and anchor `K` for all
    voters.
 The `src/` trees of
the two crates are identical. Only the benchmark harness differs (one anchor
group covering all entries instead of one per block).



---

## Requirements

- **Hardware**: x86-64 CPU, minimum 8 GB RAM (16 GB recommended)
- **Software**: Rust >= 1.81, installed via [rustup](https://rustup.rs).

---

## Repository Structure

```
├── pi1_pi2_pi3/            # Pi_1, Pi_2, Pi_3 (block shuffles with the same or different encryption keys)
├── pi4_dec_mix/            # Pi_4 (decryption mixnet)
├── pi5_dbl_mix_exp/        # Pi_5 (DbleMixExp, one exponent per voter)
├── pi6_dbl_mix_exp_single/ # Pi_6 (DbleMixExp, one exponent for all voters)
├── LICENSE-MIT
└── README.md
```

All four crates share the same internal layout:

```
<crate>/
├── Cargo.toml
├── Cargo.lock
├── src/
│   ├── lib.rs
│   ├── errors.rs
│   ├── generators.rs             # PedersenGens, BulletproofGens (CRS),
│   │                             #   and the transcript-derived fold padding
│   ├── transcript.rs
│   ├── hmac_transcript.rs        # HMAC-SHA256 transcript used by all protocols
│   ├── inner_product_proof.rs    # k-ary folding inner-product argument
│   ├── util.rs
│   ├── util_msm.rs             
│   └── r1cs/
│       ├── mod.rs
│       ├── constraint_system.rs
│       ├── linear_combination.rs
│       ├── proof.rs              # proof serialization and parsing
│       ├── prover.rs             # Prover: commitments, blinding, proof generation
│       └── verifier.rs           # Verifier: batched verification equation
├── benches/                      # Criterion benchmark harnesses (see table above)
├── tests/                        # integration tests (see table above)
└── docs/                         # notes inherited from the Bulletproofs code base
```

The four `src/` trees are deliberately near-identical: they differ only in the
protocol-specific parts of `prover.rs`, `verifier.rs`, `inner_product_proof.rs`. Keeping them separate lets each protocol be built and
measured in isolation, without feature flags cross-contaminating the timings.

---

## Building

```bash
cd pi1_pi2_pi3                      # and likewise in the other three crates
cargo build --release --lib
cargo build --release --benches --features yoloproofs
cargo build --release --tests   --features yoloproofs
```

---

## Running the Tests


```bash
cd pi1_pi2_pi3                      # and likewise in the other three crates
cargo test --release --features yoloproofs           --no-fail-fast
cargo test --release --features yoloproofs,parallel  --no-fail-fast
```

The ignored tests are cost measurements. Run them with:

```bash
cargo test --release --features yoloproofs -- --ignored --nocapture
```

---


## Running the Benchmarks

Benchmarks require the `yoloproofs` feature. Add `parallel` for multi-threaded
numbers, omit it for single-threaded numbers. For each of the configurations, the output shows a per-phase breakdown followed by totals. A summary table is printed at the end.


### Quick smoke test

`QUICK=1` selects a single small configuration (N = 1000):

```bash
cd pi1_pi2_pi3
QUICK=1 cargo bench --bench pi1 --features yoloproofs,parallel
```

**Notes**

- First benchmark run may take some minutes due to dependency compilation.
- Benchmark timings are more stable after the initial build.
- For stable numbers, run while plugged in and avoid background load.

### Reproducing Paper Results

```bash
# Pi_1, Pi_2, Pi_3
cd pi1_pi2_pi3
cargo bench --bench pi1 --features yoloproofs,parallel
cargo bench --bench pi2 --features yoloproofs,parallel
cargo bench --bench pi3 --features yoloproofs,parallel

# Pi_4
cd ../pi4_dec_mix
cargo bench --bench pi4 --features yoloproofs,parallel

# Pi_5
cd ../pi5_dbl_mix_exp
cargo bench --bench pi5 --features yoloproofs,parallel

# Pi_6
cd pi6_dbl_mix_exp_single
cargo bench --bench pi6 --features yoloproofs,parallel
```

Drop `,parallel` from any command above for the single-threaded numbers.


## Interpreting Results

The numbers in the paper were measured on an Intel Core i5-1245U (12 threads, 4.4 GHz), 16 GB RAM, Ubuntu 22.04, rustc 1.88.0.

## License

MAYA is developed by the UCLouvain Crypto Group and released under the
MIT License (see `LICENSE-MIT`). It extends the Bulletproofs library of
dalek-cryptography, distributed under the MIT License,
Copyright (c) 2018 Chain, Inc.; this notice is kept in `LICENSE-MIT`.


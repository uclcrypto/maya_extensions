# MAYA Block-Permutation Extensions

Rust implementation and benchmarks for five block-permutation shuffle-argument
protocols (Pi_1 - Pi_5) built on top of the MAYA shuffle argument
(O(log n) proof size, Ristretto255).

This repository is the reproducibility artifact accompanying the paper. It contains
three self-contained Cargo crates, each an instantiation of the same MAYA R1CS
prover/verifier core specialised to one family of protocols.

| Protocol | Description                                                     | Crate              | Benchmark          |
|----------|-----------------------------------------------------------------|--------------------|--------------------|
| **Pi_1** | Fixed block size, single encryption key                         | `pi1_pi2_pi3`      | `benches/pi1.rs`   |
| **Pi_2** | Mixed block sizes, single key                                   | `pi1_pi2_pi3`      | `benches/pi2.rs`   |
| **Pi_3** | Multiple encryption keys, per-key (per-city) permutations       | `pi1_pi2_pi3`      | `benches/pi3.rs`   |
| **Pi_4** | `DblMixExp`: shuffle-and-exponentiate, dual-key rerandomization | `pi4_dbl_mix_exp`  | `benches/pi4.rs`   |
| **Pi_5** | `DecMix`: verifiable decryption mixnet                          | `pi5_dec_mix`      | `benches/pi5.rs`   |


---

## Requirements

- **Hardware**: x86-64 CPU, minimum 8 GB RAM (16 GB recommended)
- **Software**: Rust >= 1.81, installed via [rustup](https://rustup.rs).

---

## Repository Structure

```
.
├── README.md
├── pi1_pi2_pi3/            # Pi_1, Pi_2, Pi_3 (single-group shuffle)
├── pi4_dbl_mix_exp/        # Pi_4 (DblMixExp, dual-group shuffle-and-exponentiate)
└── pi5_dec_mix/            # Pi_5 (decryption mixnet)
```

All three crates share the same internal layout:

```
<crate>/
├── Cargo.toml
├── Cargo.lock              # Pinned dependency versions for reproducibility
├── src/
│   ├── lib.rs              # Crate root, feature gates, module wiring
│   ├── errors.rs           # ProofError / MPCError / R1CSError
│   ├── generators.rs       # PedersenGens, BulletproofGens (CRS)
│   ├── transcript.rs       # TranscriptProtocol trait (Fiat-Shamir interface)
│   ├── hmac_transcript.rs  # HMAC-SHA256 transcript used by all protocols
│   ├── inner_product_proof.rs  # k-ary folding inner-product argument
│   ├── util.rs             # VecPoly/Poly arithmetic, scalar helpers (+ unit tests)
│   ├── util_msm.rs         # Rayon-chunked multiscalar multiplication (feature `parallel`)
│   └── r1cs/
│       ├── mod.rs                # Public R1CS API re-exports
│       ├── constraint_system.rs  # ConstraintSystem trait
│       ├── linear_combination.rs # LinearCombination, Variable
│       ├── proof.rs              # R1CSProof (de)serialization
│       ├── prover.rs             # Prover: commitments, blinding, proof generation
│       └── verifier.rs           # Verifier: batched verification equation
├── benches/                # Criterion benchmark harnesses (see table above)
└── docs/                   # Rustdoc protocol notes (rendered into `cargo doc`)
```

The three `src/` trees are deliberately near-identical: they differ only in the
protocol-specific parts of `prover.rs`, `verifier.rs`, `inner_product_proof.rs`
and `generators.rs`. Keeping them separate lets each protocol be built and
measured in isolation, without feature flags cross-contaminating the timings.

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
cd ../pi4_dbl_mix_exp
cargo bench --bench pi4 --features yoloproofs,parallel

# Pi_5
cd ../pi5_dec_mix
cargo bench --bench pi5 --features yoloproofs,parallel
```

Drop `,parallel` from any command above for the single-threaded numbers.


## Interpreting Results

The numbers in the paper were measured on an Intel Core i5-1245U (12 threads, 4.4 GHz), 16 GB RAM, Ubuntu 22.04, rustc 1.88.0.

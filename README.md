# Multi-Verifier Keyed-Verification Anonymous Credentials

This repository is the research prototype supporting the implementation and
benchmark claims in the accompanying paper. It is evaluator-facing artifact
code, not production-ready cryptographic software.

> **AI usage disclosure:** Cursor's generative-AI tooling assisted with
> artifact packaging, documentation, reproduction scripts, formatting, and
> maintenance fixes. The authors reviewed and validated the resulting changes.

## Paper-to-artifact mapping

- **Section 6 / Figure 13:** end-to-end mKVAC benchmark whose request NIZK uses
  the Fischlin transform with work factor 32. Run
  [`scripts/reproduce-figure-13.sh`](scripts/reproduce-figure-13.sh) and compare
  with [`expected-results/figure-13.md`](expected-results/figure-13.md).
- **Figure 18 / Appendix D:** heuristic Fiat-Shamir request-proof benchmark.
  Run [`scripts/reproduce-figure-18.sh`](scripts/reproduce-figure-18.sh) and
  compare with [`expected-results/figure-18.md`](expected-results/figure-18.md).

Both experiments use 4, 8, 32, and 64 attributes, with all attributes hidden.

## Requirements and dependencies

[Rust 1.89.0](rust-toolchain.toml) is pinned and was selected as the lowest
currently passing toolchain. With
[rustup](https://rustup.rs/) installed, invoking Cargo in this checkout obtains
the pinned toolchain; Cargo obtains the Rust dependencies.

The direct dependencies and manifest constraints in
[`Cargo.toml`](Cargo.toml) are:

- `ark-bls12-381`, `ark-ed25519`, `ark-secp256k1`, `ark-std`, `ark-poly`,
  `ark-ec`, `ark-ff`, and `ark-serialize`: `0.5.0-alpha.0`
- `rand`: `0.8.5`; `anyhow`: `1.0.75`; `hex`: `0.4.3`
- `sha2`: `0.10.8` with default features disabled
- `thiserror`: `2`; `rayon`: `1.11.0`

`Cargo.lock` is intentionally not distributed, per the artifact policy choice.
Consequently, transitive dependency resolution may change over time; the pinned
toolchain and manifest constraints represent the tested setup. No special
hardware or external datasets are required.

## Build and test

From a fresh clone:

```shell
git clone https://github.com/KULeuven-COSIC/mkvac.git
cd mkvac
cargo build --release
cargo test --release
cargo fmt --all -- --check
```

Each command should exit successfully. Compiler warnings may be emitted. If a
minimal rustup installation lacks the formatter, first run
`rustup component add rustfmt --toolchain 1.89.0`.

## Reproduce the paper benchmarks

For a quick smoke run (one round per attribute count):

```shell
BENCH_ROUNDS=1 ./scripts/reproduce-figure-13.sh
BENCH_ROUNDS=1 ./scripts/reproduce-figure-18.sh
```

For the full experiments, run the scripts without overrides; each defaults to
200 rounds:

```shell
./scripts/reproduce-figure-13.sh
./scripts/reproduce-figure-18.sh
```

The scripts print Markdown-compatible output. To retain it:

```shell
./scripts/reproduce-figure-13.sh | tee figure-13-results.md
./scripts/reproduce-figure-18.sh | tee figure-18-results.md
```

Figure 13 uses Fischlin with work factor 32; Figure 18 uses heuristic
Fiat-Shamir. Timings are hardware-dependent, while tested dimensions and
serialized sizes should agree with the expected-result files. The paper
measurements used a MacBook Pro with an Apple M4 and 24 GB RAM.

### Benchmark options

The benchmark executable accepts these environment variables:

- `BENCH_ROUNDS`: positive number of repetitions per attribute count (default:
  `200`).
- `BENCH_ATTRS`: comma-separated direct positive attribute counts, not
  exponents (default: `4,8,32,64`).
- `BENCH_SEED`: deterministic unsigned integer RNG seed (default: `42`).
- `IS_FISCHLIN`: `1` selects Fischlin; `0` selects Fiat-Shamir.
- `FISCHLIN_WORK_W`: Fischlin work factor (a power of two of at least 2).

Equivalent direct Cargo invocations for the paper parameters are:

```shell
# Figure 13: Fischlin
BENCH_ROUNDS=200 BENCH_SEED=42 BENCH_ATTRS=4,8,32,64 IS_FISCHLIN=1 FISCHLIN_WORK_W=32 \
  cargo run --release --quiet --bin benchmark

# Figure 18: Fiat-Shamir
BENCH_ROUNDS=200 BENCH_SEED=42 BENCH_ATTRS=4,8,32,64 IS_FISCHLIN=0 \
  cargo run --release --quiet --bin benchmark
```

## Interpreting output

Timing entries are in milliseconds and are reported as mean ± population standard
deviation where applicable. Serialized sizes are in KiB.

- `setup`: public-parameter generation.
- `issuerkg` and `verifierkg`: issuer and verifier key generation.
- `obt_1`: the user's first credential-obtainment step, including request-proof
  generation.
- `issue_cred`: blind credential issuance.
- `obt_2`: the user's second obtainment step, which derives the credential.
- `present`: credential presentation generation.
- `verify_show`: presentation verification.
- `tau`, `credreq`, `blind`, `cred`, and `pres`: serialized sizes of the
  verifier authorization, credential request, blind credential, final
  credential, and presentation, respectively.

## Repository organization

```text
.
├── bin/benchmark.rs                 # benchmark executable
├── expected-results/
│   ├── figure-13.md
│   └── figure-18.md
├── paper/                           # accompanying paper
├── scripts/
│   ├── reproduce-figure-13.sh
│   └── reproduce-figure-18.sh
├── src/
│   ├── mkvak/                       # mKVAC protocol and request proofs
│   └── saga/                        # SAGA building block
├── Cargo.toml                       # crate and dependency manifest
├── rust-toolchain.toml              # pinned Rust toolchain
└── LICENSE                          # MIT license
```

`src/mkvak/` implements the mKVAC protocol, including Fiat-Shamir and Fischlin
request proofs; `src/saga/` implements the SAGA primitive.
`bin/benchmark.rs` is the benchmark driver, `scripts/` contains paper
reproduction entry points, and `expected-results/` provides comparison data.
`paper/` contains the accompanying paper. `Cargo.toml`,
`rust-toolchain.toml`, and `LICENSE` define the crate, tested toolchain, and
license.

## License and team

The artifact is distributed under the [MIT License](LICENSE). Third-party
dependencies retain their own licenses.

- [Jan Bobolz](https://jan-bobolz.de/)
- [Emad Heydari Beni](https://heydari.be)
- [Anja Lehmann](https://hpi.de/lehmann/team/anja-lehmann.html)
- [Omid Mirzamohammadi](https://www.esat.kuleuven.be/cosic/people/person/?u=u0159898)
- [Cavit Özbay](https://hpi.de/lehmann/team/cavit-oezbay.html)
- [Mahdi Sedaghat](https://mahdi171.github.io/)

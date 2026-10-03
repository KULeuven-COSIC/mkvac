#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$repo_root"

BENCH_ROUNDS="${BENCH_ROUNDS:-200}" \
BENCH_SEED=42 \
BENCH_ATTRS=4,8,32,64 \
IS_FISCHLIN=0 \
FISCHLIN_WORK_W=16 \
exec cargo run --release --quiet --bin benchmark

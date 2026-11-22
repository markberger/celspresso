#!/usr/bin/env bash
# Local quality gates: lint, types, tests, and coverage floors.
# Usage: scripts/check.sh            (everything)
#        scripts/check.sh --fast     (skip the Rust coverage build)
set -euo pipefail
cd "$(dirname "$0")/.."

# Coverage floors. Ratchet these up as coverage improves; never lower them.
# Python floor lives in pyproject.toml ([tool.coverage.report] fail_under).
RUST_LINE_FLOOR=83

step() { printf '\n\033[1m==> %s\033[0m\n' "$*"; }

step "ruff lint"
uv run ruff check python tests benchmarks

step "ruff format"
uv run ruff format --check python tests benchmarks

step "pyright"
uv run pyright python

step "build extension"
uv run maturin develop --release --quiet

step "python tests + coverage (floor in pyproject.toml)"
uv run pytest -q --cov --cov-report=term-missing

step "cel-spec conformance ratchet (fails if a previously passing test regresses)"
git submodule update --init --quiet third_party/cel-spec
cargo run -q -p celspresso-conformance --release | tail -n 3

if [[ "${1:-}" != "--fast" ]]; then
  step "rust tests + conformance coverage (floor ${RUST_LINE_FLOOR}% lines)"
  # unit tests and the cel-spec suite both count: the suite is the evaluator's main test
  cargo llvm-cov clean --workspace
  cargo llvm-cov --no-report --workspace --exclude celspresso-py --exclude celspresso-conformance
  cargo llvm-cov run --no-report -q -p celspresso-conformance > /dev/null
  cargo llvm-cov report --summary-only --ignore-filename-regex 'celspresso-conformance' \
    --fail-under-lines "${RUST_LINE_FLOOR}"
fi

step "all gates passed"

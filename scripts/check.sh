#!/usr/bin/env bash
# Local quality gates: lint, types, tests, and coverage floors.
# Usage: scripts/check.sh            (everything)
#        scripts/check.sh --fast     (skip the Rust coverage build)
set -euo pipefail
cd "$(dirname "$0")/.."

# Coverage floors. Ratchet these up as coverage improves; never lower them.
# Python floor lives in pyproject.toml ([tool.coverage.report] fail_under).
RUST_LINE_FLOOR=73

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

if [[ "${1:-}" != "--fast" ]]; then
  step "rust tests + coverage (floor ${RUST_LINE_FLOOR}% lines)"
  cargo llvm-cov --workspace --exclude celspresso-py --summary-only \
    --fail-under-lines "${RUST_LINE_FLOOR}"
fi

step "all gates passed"

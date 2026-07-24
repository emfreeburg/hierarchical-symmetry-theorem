#!/usr/bin/env bash
# Freeburg formalization — the full verification gate, one command.
#
#   ./check.sh
#
# Reproduces the three checks that define "verified" for this library:
#   1. `lake build`      — every module compiles (the kernel checks every proof).
#   2. `AxiomAudit.lean` — an environment walk over EVERY constant compiled
#      from the Freeburg.* modules, failing unless each depends only on
#      Lean's three standard axioms [propext, Classical.choice, Quot.sound].
#      This soundly rules out `sorry`/`admit` (they introduce `sorryAx`),
#      `native_decide` (`Lean.ofReduceBool`), and any custom axiom.
#   3. An advisory grep for escape hatches in the source text.
#
# Toolchain is pinned by `lean-toolchain`; Mathlib is pinned by
# `lake-manifest.json`. First run on a fresh machine:
#   lake exe cache get   # pulls the prebuilt Mathlib cache (multi-GB, once)
set -euo pipefail
cd "$(dirname "$0")"

echo "== 1/3 lake build =="
lake build

echo "== 2/3 axiom audit (whole library) =="
lake env lean AxiomAudit.lean

echo "== 3/3 escape-hatch grep (advisory; audit above is the sound check) =="
if grep -rnE '\bsorry\b|\badmit\b|native_decide|^axiom |\bunsafe\b|partial def|\bopaque\b' \
    --include='*.lean' Freeburg Freeburg.lean \
    | grep -vE 'sorry-free|rules out'; then
  echo "grep found matches above — inspect them (docstring prose is fine)."
else
  echo "clean."
fi

echo "ALL GATES PASS"

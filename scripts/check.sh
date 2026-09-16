#!/usr/bin/env bash
# Fail if any module contains a `sorry` or depends on a non-standard axiom.
set -uo pipefail
cd "$(dirname "$0")/.."

# `sorry` as code, not as documentation: a module docstring may legitimately
# say a development contains no `sorry`, and that must not trip the check.  A
# real `sorry` would also show up as `sorryAx` in the axiom check below, so this
# grep is the early warning rather than the guarantee.
if grep -rn --include='*.lean' -E '\bsorry\b' FourColor/ | grep -v '`sorry`' ; then
  echo "FAIL: sorry found" >&2; exit 1
fi

# Constructs that would put something beyond the kernel into the trusted base,
# or that a mathlib reviewer would reject on sight.  `native_decide` trusts the
# compiler; `axiom` adds to the base directly; `unsafe`/`opaque`/`partial` and
# the code-generator attributes all mean a definition the kernel cannot see
# through.  None of these is acceptable in a proof meant to be believed.
if grep -rn --include='*.lean' -E \
    '\bnative_decide\b|^axiom |^ *axiom |\bpartial def\b|\bunsafe\b|^opaque |@\[implemented_by|@\[extern' \
    FourColor/ ; then
  echo "FAIL: native_decide, axiom, partial, unsafe, opaque or a code-generator attribute found" >&2
  exit 1
fi

# Scratch files must not ship: they are not reachable from the root module, so
# they never enter `lake build`, but a reader finding them would reasonably ask
# what they are doing in a finished development.
if ls FourColor/Research*.lean FourColor/*Probe*.lean >/dev/null 2>&1; then
  echo "FAIL: scratch modules still present:" >&2
  ls FourColor/Research*.lean FourColor/*Probe*.lean 2>/dev/null >&2
  exit 1
fi

lake build >/dev/null || { echo "FAIL: build" >&2; exit 1; }

# Anti-vacuity negative controls: a proof can be sorry-free, axiom-clean and
# still worthless if its decision procedures accept everything.  Each example in
# Audit.lean says some checker the proof relies on answers `false` somewhere.
audit=$(lake env lean scripts/Audit.lean 2>&1)
if echo "$audit" | grep -qE '^.*error'; then
  echo "$audit" >&2; echo "FAIL: anti-vacuity audit" >&2; exit 1
fi
echo "anti-vacuity audit: negative controls pass"

out=$(lake env lean scripts/Check.lean 2>&1)
echo "$out"
if echo "$out" | grep -qE 'error|sorryAx|ofReduceBool'; then
  echo "FAIL: axiom check" >&2; exit 1
fi

#!/usr/bin/env bash
# Fail if any module contains a `sorry` or depends on a non-standard axiom.
set -uo pipefail
cd "$(dirname "$0")/.."

# `sorry` as code, not as documentation: a module docstring may legitimately
# say a development contains no `sorry`, and that must not trip the check.  A
# real `sorry` would also show up as `sorryAx` in the axiom check below, so this
# grep is the early warning rather than the guarantee.
if grep -rn --include='*.lean' -E '\bsorry\b' FourColor/ FourColor.lean scripts/*.lean | grep -v '`sorry`' ; then
  echo "FAIL: sorry found" >&2; exit 1
fi

# Constructs that would put something beyond the kernel into the trusted base,
# or that a mathlib reviewer would reject on sight.  `native_decide` trusts the
# compiler; `axiom` adds to the base directly; `unsafe`/`opaque`/`partial` and
# the code-generator attributes all mean a definition the kernel cannot see
# through.  None of these is acceptable in a proof meant to be believed.
# `[[:space:]]*` rather than ` *`, so a tab-indented `axiom` cannot slip past;
# `sorryAx` is listed separately because `\bsorry\b` does not match it; and
# `debug.skipKernelTC` is the one option that would disable the kernel check
# this whole file is about, so it is named explicitly.
if grep -rn --include='*.lean' -E \
    '\bnative_decide\b|\bsorryAx\b|^[[:space:]]*(private |protected |noncomputable )*axiom |\bpartial def\b|\bunsafe\b|^[[:space:]]*opaque |@\[implemented_by|@\[extern|debug\.skipKernelTC' \
    FourColor/ FourColor.lean scripts/*.lean ; then
  echo "FAIL: native_decide, sorryAx, axiom, partial, unsafe, opaque, skipKernelTC or a code-generator attribute found" >&2
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

# Deliberately not `lake build`: Lake tracks its own trace files and knows
# nothing about the oleans `build_pool.py` writes, so it would rebuild the whole
# development — and it starts one job per hardware thread, which with modules
# that peak at 20 GB is how a large machine runs out of memory.  build_pool.py
# is incremental and schedules under a memory budget, and is a no-op when
# `build.sh` has just run it.
scripts/build_pool.py || { echo "FAIL: build" >&2; exit 1; }

# Anti-vacuity negative controls: a proof can be sorry-free, axiom-clean and
# still worthless if its decision procedures accept everything.  Each example in
# Audit.lean says some checker the proof relies on answers `false` somewhere.
# The exit status matters as much as the text: an OOM kill, a segfault or a
# missing `lake` produces no line containing "error", and grepping alone would
# score that as a pass.  Modules here peak at 20 GB, so an OOM-killed checker is
# the likeliest failure of all.
audit=$(lake env lean scripts/Audit.lean 2>&1); rc=$?
if [ $rc -ne 0 ]; then
  echo "$audit" >&2; echo "FAIL: anti-vacuity audit exited $rc" >&2; exit 1
fi
if echo "$audit" | grep -qE '^.*error'; then
  echo "$audit" >&2; echo "FAIL: anti-vacuity audit" >&2; exit 1
fi
echo "anti-vacuity audit: negative controls pass"

out=$(lake env lean scripts/Check.lean 2>&1); rc=$?
echo "$out"
if [ $rc -ne 0 ]; then
  echo "FAIL: axiom check exited $rc" >&2; exit 1
fi
if echo "$out" | grep -qE 'error|sorryAx|ofReduceBool'; then
  echo "FAIL: axiom check" >&2; exit 1
fi
# Check.lean reports THEOREM OUTSTANDING, not an error, when the theorem is
# absent -- so a build that dropped it would otherwise pass here in silence.
# Demand the positive statement rather than the absence of a negative one.
if ! echo "$out" | grep -q 'THEOREM PROVED: FourColor.fourColorTheorem'; then
  echo "FAIL: the theorem was not proved in this build" >&2; exit 1
fi

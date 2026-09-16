#!/usr/bin/env bash
# Build and verify the four colour theorem, from a bare checkout, in one command.
#
#   ./build.sh                    # sizes itself to the machine
#   JOBS=8 MEMORY=40 ./build.sh   # or pin the job count and the memory budget
#
# The four steps, each a no-op when it has nothing left to do:
#
#   1. Mathlib, from the central cache.
#   2. The reducibility certificates (`FourColor/Bulk/Cfg`, `FourColor/Mask`),
#      regenerated from `FourColor/Configurations.lean` if they are not present.
#      About one core-hour.  See `scripts/README.md`.
#   3. The `FourColor` modules, about 11 core-hours.  `build_pool.py` schedules
#      them against the cost table in `scripts/module_cost.tsv`, under a job
#      cap and a memory budget it derives from the machine; see its `--help`.
#   4. `scripts/check.sh`: the axioms of `fourColorTheorem`, no `sorry`, no
#      `native_decide`, and the anti-vacuity controls of `scripts/Audit.lean`.
#
# On success the last lines read
#
#   THEOREM PROVED: FourColor.fourColorTheorem : FourColor.FourColorTheorem depends only on [...]
set -euo pipefail
cd "$(dirname "$0")"

echo "== Mathlib (from the cache)"
lake exe cache get

if [ ! -d FourColor/Bulk/Cfg ]; then
  echo "== reducibility certificates (not present; regenerating, about one core-hour)"
  scripts/gen_certificates.sh certgen "$(nproc)"
fi

echo "== the FourColor modules"
scripts/build_pool.py ${JOBS:+--jobs "$JOBS"} ${MEMORY:+--memory "$MEMORY"}

echo "== verifying"
exec scripts/check.sh

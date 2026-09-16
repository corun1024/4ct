#!/usr/bin/env bash
# Build and verify the four colour theorem, from a bare checkout, in one command.
#
#   ./build.sh            # as many parallel `lean` jobs as memory comfortably allows
#   JOBS=8 ./build.sh     # or pin the job count yourself
#
# The four steps, each a no-op when it has nothing left to do:
#
#   1. Mathlib, from the central cache.
#   2. The reducibility certificates (`FourColor/Bulk/Cfg`, `FourColor/Mask`),
#      regenerated from `FourColor/Configurations.lean` if they are not present.
#      About one core-hour.  See `scripts/README.md`.
#   3. The `FourColor` modules.  About 11 core-hours; a single module can peak
#      at 8.3 GB, which is what bounds the job count.
#   4. `scripts/check.sh`: the axioms of `fourColorTheorem`, no `sorry`, no
#      `native_decide`, and the anti-vacuity controls of `scripts/Audit.lean`.
#
# On success the last lines read
#
#   THEOREM PROVED: FourColor.fourColorTheorem depends only on [propext, Classical.choice, Quot.sound]
set -euo pipefail
cd "$(dirname "$0")"

# 8.3 GB is the largest module's peak, so leave it that much room per job.
if [ -z "${JOBS:-}" ]; then
  mem_gb=$(awk '/MemTotal/ {print int($2 / 1024 / 1024)}' /proc/meminfo 2>/dev/null || echo 8)
  JOBS=$(( mem_gb / 8 ))
  cpus=$(nproc)
  [ "$JOBS" -gt "$cpus" ] && JOBS=$cpus
  [ "$JOBS" -lt 1 ] && JOBS=1
fi

echo "== Mathlib (from the cache)"
lake exe cache get

if [ ! -d FourColor/Bulk/Cfg ]; then
  echo "== reducibility certificates (not present; regenerating, about one core-hour)"
  scripts/gen_certificates.sh certgen "$(nproc)"
fi

echo "== the FourColor modules ($JOBS parallel jobs)"
scripts/build_pool.py --jobs "$JOBS"

echo "== verifying"
exec scripts/check.sh

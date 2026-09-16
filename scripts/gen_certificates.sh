#!/usr/bin/env bash
# Regenerate every reducibility certificate module from `FourColor/Configurations.lean`.
#
#   tools/cpc.py       the configurations' colourings and contract colourings, as traces
#   tools/planes.c     the bulk certificate: rank/witness/choice planes of the one-chord rule,
#                      and the residual contract colourings it leaves
#   tools/residual.c   the residual certificate: ranked witnesses for the mask walk and,
#                      per chord, the entries the chord settles
#   scripts/gen_*.py   the Lean modules
#
# Nothing in the proof trusts these tools: every module they write is checked by the
# kernel against the theorems of FourColor/Bulk and FourColor/Mask*.lean.
#
# Usage: scripts/gen_certificates.sh [workdir] [jobs]    (from the project root)
set -euo pipefail
cd "$(dirname "$0")/.."
W=${1:-certgen}
J=${2:-$(nproc)}
mkdir -p "$W"/gen "$W"/planes "$W"/logs "$W"/hybc
mkdir -p "$W"/bin
gcc -O2 -o "$W"/bin/planes tools/planes.c
gcc -O2 -o "$W"/bin/residual tools/residual.c

echo "== inputs (cpcolor and contract colourings of the 633 configurations)"
python3 tools/cpc.py FourColor/Configurations.lean "$W"/gen

echo "== bulk certificates (planes)"
seq 0 632 | xargs -P "$J" -I{} sh -c 'EMIT='"$W"'/planes/{}.planes '"$W"'/bin/planes < '"$W"'/gen/{}.in > '"$W"'/logs/{}.out 2> '"$W"'/logs/{}.err && gzip -3 -f '"$W"'/planes/{}.planes'
# the configurations the one-chord rule does not settle
: > "$W"/failing.txt
for i in $(seq 0 632); do
  r=$(grep -o 'residual_orbits=[0-9]*' "$W"/logs/$i.out | head -1 | cut -d= -f2)
  [ "${r:-0}" -gt 0 ] && echo "$i" >> "$W"/failing.txt
done
python3 - "$W" <<'PY'
import sys
w = sys.argv[1]
fail = set(int(x) for x in open(f'{w}/failing.txt').read().split())
open(f'{w}/bulk.txt', 'w').write(' '.join(str(i) for i in range(633) if i not in fail))
print(f'{len(fail)} residual configurations, {633 - len(fail)} settled by the bulk certificate')
PY

echo "== residual certificates"
tr ' \n' '\n\n' < "$W"/failing.txt | grep . | xargs -P "$J" -I{} sh -c 'EMIT='"$W"'/hybc/{}.txt '"$W"'/bin/residual < '"$W"'/gen/{}.in > '"$W"'/hybc/{}.log 2>&1'

echo "== Lean modules"
rm -f FourColor/Bulk/Cfg/Grp*.lean FourColor/Bulk/Cfg/Hyb*.lean FourColor/Mask/Cfg*.lean
python3 scripts/gen_groups.py "$W"/failing.txt --gen "$W"/gen --out "$W"/groups.txt > /dev/null
xargs -P "$J" -L 1 sh -c 'python3 scripts/gen_bulk_jobs.py '"$W"'/planes '"$W"'/gen FourColor/Bulk/Cfg --group "$0" "$@" > /dev/null' < "$W"/groups.txt
tr ' \n' '\n\n' < "$W"/failing.txt | grep . | xargs -P "$J" -I{} sh -c 'python3 scripts/gen_maskc_jobs.py '"$W"'/planes '"$W"'/gen '"$W"'/hybc FourColor/Mask {} > '"$W"'/logs/mask_{}.txt && python3 scripts/gen_hybt_jobs.py '"$W"'/planes '"$W"'/gen '"$W"'/hybc FourColor/Bulk/Cfg {} > '"$W"'/logs/hyb_{}.txt'
python3 scripts/gen_all.py "$W"/failing.txt --groups "$W"/groups.txt
echo "== done: $(ls FourColor/Bulk/Cfg/Grp*.lean | wc -l) bulk groups, $(ls FourColor/Mask/Cfg*.lean | wc -l) walks, $(ls FourColor/Bulk/Cfg/Hyb*.lean | wc -l) bridge modules"

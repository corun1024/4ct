#!/usr/bin/env python3
"""Generate the bulk reducibility module of a configuration.

The module carries three sets of bit planes over the 3^(n-1) ring traces of a
configuration — the rank of every trace, the least rank among its six colour
permutations, and the position it is argued with — and proves, one kernel
computation per declaration, the checks `Bulk.cfReducible_of_bulkChecks` asks
for: the witness planes are the permutation minimum of the rank planes, the
rank-zero traces are colourings, every argued position is a real chord end, and
for each of the n(n-1)/2 position pairs the pair check passes.  The colourings
and the contract colourings are computed by the kernel from the construction
program, so nothing about them is emitted.

Usage: scripts/gen_bulk_jobs.py <planesdir> <gendir> <outdir> <idx>...
       scripts/gen_bulk_jobs.py <planesdir> <gendir> <outdir> --group <name> <idx>...

The first form writes one module `<outdir>/Cfg<idx>.lean` per configuration; the
second writes every listed configuration into the single module
`<outdir>/<name>.lean`, each in its own namespace `FourColor.Bulk.Cfg<idx>`, so
that the fixed per-module cost of the build is paid once for the group.  The
declarations are the same either way.

`<gendir>/<idx>.in` starts with the line `ring <n>`.

`<planesdir>/<idx>.planes[.gz]` is the closure engine's dump: `rank0..6`,
`rmin0..6`, `choice0..3` as hex chunks of 2^14 bits, least significant first.
"""
import gzip
import os
import sys

PAIR_GROUP = 8

SEP = ",\n  "
SEP2 = "\n  "
NL = "\n"

CHUNK_BITS = 16384


def read_planes(path):
    op = gzip.open if path.endswith('.gz') else open
    planes, cur = {}, None
    with op(path, 'rt') as f:
        for line in f:
            t = line.split()
            if not t:
                continue
            if t[0].startswith('0x'):
                planes[cur].append(t[0])
            else:
                cur = t[0]
                planes[cur] = []
    return planes


def mask_out(chunks, good):
    """Clear in `chunks` every bit set in `good` (both least-significant-chunk-first)."""
    out = []
    for c, g in zip(chunks, good + ['0x0'] * (len(chunks) - len(good))):
        out.append(f'0x{int(c, 16) & ~int(g, 16):x}')
    return out


def lit(chunks):
    """A `bignat%` literal from hex chunks (least significant first)."""
    # drop leading zero chunks at the top to keep the source short
    while len(chunks) > 1 and chunks[-1] == '0x0':
        chunks = chunks[:-1]
    return 'bignat% [' + ', '.join(chunks) + ']'


HEADER = """import FourColor.Bulk.Reducible
import FourColor.Bulk.Lit
import FourColor.Configurations

/-!
{doc}
-/

set_option Elab.async false
set_option maxRecDepth 100000
"""


def load(idx, planesdir, ring):
    """The planes of a configuration, with rank zero restored on the colourings."""
    path = os.path.join(planesdir, f'{idx}.planes.gz')
    if not os.path.exists(path):
        path = path[:-3]
    P = read_planes(path)
    # rank zero for the colourings: the engine wrote the top rank there, the witness
    # planes use zero, and the good check wants zero
    good = P['good']
    R = [mask_out(P[f'rank{b}'], good) for b in range(7)]
    C = [P[f'choice{b}'] for b in range(4)]
    return R, C


def body(idx, ring, R, C):
    """The declarations of one configuration, as the lines between its namespace
    opening and closing (the text is the same whichever module carries it)."""
    n = ring
    m = n - 1
    pairs = [(p, q) for q in range(n) for p in range(q)]
    lines = []
    L = lines.append
    L(f"""/-- The configuration. -/
def cf : Config := theConfigs[{idx}]!

/-- The number of stored digits: the ring size less one. -/
def m : ℕ := {m}

/-- Rank planes: bit `b` of the rank of trace `i`; all bits set means "not certified". -/
def R : List ℕ := [
  {SEP.join(lit(r) for r in R)}]

/-- Witness planes: the least rank among the six colour permutations of each trace. -/
def H : List ℕ := minPerm m R

/-- Choice planes: the position each certified trace is argued with. -/
def C : List ℕ := [
  {SEP.join(lit(c) for c in C)}]

theorem hcf : cprsize cf.prog = m + 1 := by decide +kernel

theorem hH : H = minPerm m R := rfl

theorem hgood : goodCheck m R cf.prog = true := by decide +kernel

theorem hchoice : choiceCheck m R C = true := by decide +kernel

theorem hctr : contractCheck cf m R = true := by decide +kernel
""")
    # the pair checks, in groups: the witness planes `H` are recomputed once per
    # declaration, so a group shares that cost, and a group of eight keeps the
    # declaration's retained memory under a gigabyte
    groups = [pairs[i:i + PAIR_GROUP] for i in range(0, len(pairs), PAIR_GROUP)]
    for g, grp in enumerate(groups):
        L(f"""/-- Pair checks {grp[0]} to {grp[-1]}. -/
theorem pairs_{g} : [{", ".join(f"({p}, {q})" for (p, q) in grp)}].all
    (fun pq => pairOk m pq.1 pq.2 R H (pairChoice m R C pq.1 pq.2)) = true := by
  decide +kernel
""")
    L(f"""/-- All {len(pairs)} pair checks, assembled without recomputation. -/
theorem hpairs : allPairs m R H C = true := by
  rw [allPairs, show pairList m = {" ++ ".join("[" + ", ".join(f"({p}, {q})" for (p, q) in grp) + "]" for grp in groups)} from by decide]
  simp only [List.all_append, Bool.and_true, Bool.true_and,
    {", ".join(f"pairs_{g}" for g in range(len(groups)))}]

/-- **Configuration {idx + 1} is C-reducible.** -/
theorem reducible : ReducibleInRange {idx} ({idx} + 1) theConfigs :=
  reducible_range_one
    (cfReducible_of_bulkChecks cf m hcf R H C (by rw [hH, length_minPerm]) (by decide) hH hgood hchoice hpairs hctr)
""")
    return lines


def emit(idx, planesdir, outdir, ring):
    """One module `Cfg<idx>.lean` for one configuration."""
    n = ring
    m = n - 1
    R, C = load(idx, planesdir, ring)
    doc = f"""# Configuration {idx + 1} is C-reducible

Ring size {n}: {3 ** m} traces, argued in bulk.  Generated by
`scripts/gen_bulk_jobs.py`; every declaration below is one kernel computation."""
    lines = [HEADER.format(doc=doc) + f"""
namespace FourColor
namespace Bulk
namespace Cfg{idx:03d}
"""]
    lines += body(idx, ring, R, C)
    lines.append(f"""end Cfg{idx:03d}
end Bulk
end FourColor
""")
    os.makedirs(outdir, exist_ok=True)
    out = os.path.join(outdir, f'Cfg{idx:03d}.lean')
    open(out, 'w').write(NL.join(lines))
    return out


def emit_group(name, cfgs, planesdir, outdir):
    """One module `<name>.lean` for the configurations `cfgs`, a list of
    `(idx, ring)`, each in its own namespace `FourColor.Bulk.Cfg<idx>`."""
    doc = [f'# Configurations {", ".join(str(i + 1) for i, _ in cfgs)} are C-reducible', '',
           f'Group `{name}`, argued in bulk.  Generated by `scripts/gen_bulk_jobs.py`;',
           'every declaration below is one kernel computation.', '']
    for i, ring in cfgs:
        doc.append(f'* configuration {i + 1} (`Cfg{i:03d}`): ring size {ring}, {3 ** (ring - 1)} traces')
    lines = [HEADER.format(doc=NL.join(doc))]
    for i, ring in cfgs:
        R, C = load(i, planesdir, ring)
        lines.append(f'namespace FourColor.Bulk.Cfg{i:03d}\n')
        lines += body(i, ring, R, C)
        lines.append(f'end FourColor.Bulk.Cfg{i:03d}\n')
    os.makedirs(outdir, exist_ok=True)
    out = os.path.join(outdir, f'{name}.lean')
    open(out, 'w').write(NL.join(lines))
    return out


def ring_of(gendir, i):
    with open(os.path.join(gendir, f'{i}.in')) as f:
        return int(f.readline().split()[1])


if __name__ == '__main__':
    # usage: gen_bulk_jobs.py <planesdir> <gendir> <outdir> [--group <name>] <idx>...
    planesdir, gendir, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    rest = sys.argv[4:]
    if rest and rest[0] == '--group':
        name = rest[1]
        cfgs = [(int(x), ring_of(gendir, int(x))) for x in rest[2:]]
        out = emit_group(name, cfgs, planesdir, outdir)
        print(f'{name}: ' + ' '.join(f'cfg{i:03d} (ring {r})' for i, r in cfgs) + f' -> {out}')
    else:
        for i in (int(x) for x in rest):
            ring = ring_of(gendir, i)
            out = emit(i, planesdir, outdir, ring)
            print(f'cfg{i:03d}: ring {ring} -> {out}')

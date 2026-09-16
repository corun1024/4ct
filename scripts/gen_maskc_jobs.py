#!/usr/bin/env python3
"""Emit the chord-aware mask certificate of a residual configuration.

Like `gen_mask_jobs.py`, the walk carries a bitmask over a universe of traces
and asks one question at each leaf.  What is new: it also carries the set of
certified traces still to justify, and every closed chord `(q, p)` removes
from it the traces `okArr[q][p]` names — the traces one of whose three flips
along the chord is known or ranks lower (see `scripts/bulkspace.py`).  A
subtree with nothing left to justify is cut, which removes most of the tree.

The universe holds the certified traces and only the witnesses the walk needs:
the walk is simulated once over every witness the certificate names, and a
small set of witnesses meeting every surviving leaf is kept (`reduce_universe`).

The tree of theorems is split adaptively: the walk is simulated here, and a
subtree becomes one `decide +kernel` declaration when its node count fits a
memory budget, so that the kernel releases each subtree's masks in turn.

Usage: gen_maskc_jobs.py <planesdir> <gendir> <certdir> <outdir> <idx>...
"""
import os
import sys

SEP = ",\n  "
SEP2 = "\n  "
NL = "\n"

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_bulk_jobs as B
import certdata as G
import certdata as M
import bulkspace as BS

# retained bytes per node ≈ 4 wide results; keep a leaf declaration under this
LEAF_BYTES = 600 * 1000 * 1000
LEAF_NODES_MAX = 150000
DMAX = 9          # deepest split point


def read_ok(path):
    ok = {}
    for line in open(path):
        f = line.split()
        if f and f[0] == 'OK':
            q, p, cnt = int(f[1]), int(f[2]), int(f[3])
            ok[(q, p)] = [int(x) for x in f[4:4 + cnt]]
    return ok


def walk_leaves(n, col, certmask, exact, lower, okS, N, on_leaf):
    """Simulate the walk of `emit` and call `on_leaf(r, live)` at every surviving
    leaf: `r` is the lowest rank present among the certified traces still live,
    `live` the live mask.  Returns the node count, which does not depend on the
    witnesses (a subtree is cut on the certified traces alone)."""
    sys.setrecursionlimit(10000)
    full = (1 << N) - 1

    def mm(p, c):
        return col[(p, str(c))]

    def rec(d, stack, a, c):
        if a & c == 0:
            return 1
        if d == n:
            if not stack:
                A = a & c
                r = 0
                while A & exact[r] == 0:
                    r += 1
                on_leaf(r, a)
            return 1
        cnt = 1
        cnt += rec(d + 1, stack, a & mm(d, 1), c)
        cnt += rec(d + 1, stack + [d], a & (mm(d, 2) | mm(d, 3)), c)
        if stack:
            q = stack[-1]
            c2 = c ^ (c & okS[(q, d)])
            cnt += rec(d + 1, stack[:-1], a & ((mm(d, 2) & mm(q, 2)) | (mm(d, 3) & mm(q, 3))), c2)
            cnt += rec(d + 1, stack[:-1], a & ((mm(d, 2) & mm(q, 3)) | (mm(d, 3) & mm(q, 2))), c2)
        return cnt

    return rec(0, [], full, certmask)


def cover(sets):
    """A small set of indices meeting every set in `sets` (lists of indices):
    greedy, always taking the index in the most sets not yet met."""
    import heapq
    from collections import defaultdict
    holds = defaultdict(list)
    for i, bits in enumerate(sets):
        for b in bits:
            holds[b].append(i)
    freq = {b: len(v) for b, v in holds.items()}
    heap = [(-c, b) for b, c in freq.items()]
    heapq.heapify(heap)
    met = [False] * len(sets)
    chosen = []
    while heap:
        c, b = heapq.heappop(heap)
        if freq[b] == 0:
            continue
        if -c != freq[b]:                    # stale count: re-queue
            heapq.heappush(heap, (-freq[b], b))
            continue
        chosen.append(b)
        for i in holds[b]:
            if not met[i]:
                met[i] = True
                for b2 in sets[i]:
                    freq[b2] -= 1
    assert all(met)
    return chosen


def reduce_universe(idx, ring, entries, W, okS):
    """Keep only the witnesses the walk needs.

    At a surviving leaf one live witness below the lowest rank present suffices,
    so the walk is simulated once over the full universe `W` (as `build_wit`
    made it), recording at each leaf which witnesses could serve — a leaf where
    an entry serves needs none — and a small set meeting every leaf is chosen
    greedily.  The certificate is then re-read with only the answers naming
    kept traces, so every field is rebuilt by the very same construction over
    the reduced universe, and the walk is simulated again over it to check
    that every leaf still passes."""
    (_, N, col, certmask, exact, lower, maxr, goodmask, wl, goods, universe) = W
    E = len(entries)
    entmask = (1 << E) - 1
    stats = [0, 0]       # surviving leaves, leaves needing a witness
    seen = set()         # the distinct candidate sets, as tuples of indices

    def record(r, a):
        live = a & lower[r]
        if live == 0:
            raise RuntimeError(f'cfg{idx}: leaf test fails on the full universe (rank {r})')
        stats[0] += 1
        if live & entmask:
            return               # an entry below rank r is live: no witness needed
        stats[1] += 1
        bits = []
        while live:
            low = live & -live
            bits.append(low.bit_length() - 1)
            live ^= low
        seen.add(tuple(bits))

    total = walk_leaves(ring, col, certmask, exact, lower, okS, N, record)
    chosen = cover(sorted(seen))
    keep = set(t for t, _, _ in entries)
    keep.update(universe[b] for b in chosen)
    filtered = [(t, r, [x for x in ans if M.complete(M.flip(t[:-1], x[1])) in keep])
                for t, r, ans in entries]
    W2 = G.build_wit_entries(idx, ring, filtered)
    (_, N2, col2, certmask2, exact2, lower2, maxr2, _, _, _, universe2) = W2
    assert universe2[:E] == universe[:E] and N2 == E + len(chosen)
    assert certmask2 == certmask and exact2 == exact and maxr2 == maxr

    def check(r, a):
        if a & lower2[r] == 0:
            raise RuntimeError(f'cfg{idx}: leaf test fails on the reduced universe (rank {r})')

    total2 = walk_leaves(ring, col2, certmask2, exact2, lower2, okS, N2, check)
    assert total2 == total, f'cfg{idx}: node count changed ({total} -> {total2})'
    print(f'cfg{idx:03d}: universe {N} -> {N2} ({E} entries, {len(chosen)} of {N - E} witnesses '
          f'kept; {total} nodes, {stats[0]} leaves, {stats[1]} needing a witness, '
          f'{len(seen)} distinct candidate sets)')
    return W2


def build_all(idx, planesdir, gendir, certdir):
    """Everything both the mask module and the bridge need."""
    with open(os.path.join(gendir, f'{idx}.in')) as f:
        n = int(f.readline().split()[1])
    m = n - 1
    path = os.path.join(planesdir, f'{idx}.planes.gz')
    P = B.read_planes(path if os.path.exists(path) else path[:-3])
    good = P['good']
    Rchunks = [B.mask_out(P[f'rank{b}'], good) for b in range(7)]
    R = [BS.big_of_chunks(c) for c in Rchunks]
    ring, entries = M.read_cert(os.path.join(certdir, f'{idx}.txt'))
    W = G.build_wit_entries(idx, ring, entries)
    (_, N, col, certmask, exact, lower, maxr, goodmask, wl, goods, universe) = W
    # bulk space
    bk = BS.Bulk(m)
    Kb = bk.known(R)
    ebig = [BS.big_index(t, m) for t, _, _ in entries]
    elev = [r for _, r, _ in entries]
    valR, valH, nplanes = bk.residual_planes(Kb, ebig, elev, maxr)
    settled = bk.settled(valR, valH, ebig, elev, n)
    # cross-check the C extractor's lists
    cok = read_ok(os.path.join(certdir, f'{idx}.txt'))
    for (q, p), s in settled.items():
        mine = [i for i in range(len(entries)) if s[i]]
        if cok.get((q, p)) is not None and cok[(q, p)] != mine:
            print(f'cfg{idx}: chord ({q},{p}) settles {len(mine)} here, {len(cok[(q, p)])} in C', file=sys.stderr)
    okS = {}
    for (q, p), s in settled.items():
        v = 0
        for i in np_nonzero(s):
            v |= 1 << i          # entry i sits at universe position i
        okS[(q, p)] = v
    # only the witnesses the walk needs
    (_, N, col, certmask, exact, lower, maxr, goodmask, wl, goods, universe) = \
        reduce_universe(idx, ring, entries, W, okS)
    return dict(n=n, m=m, N=N, col=col, certmask=certmask, exact=exact, lower=lower, maxr=maxr,
                goodmask=goodmask, wl=wl, goods=goods, universe=universe, entries=entries,
                Rchunks=Rchunks, P=P, Kb=Kb, valR=valR, valH=valH, nplanes=nplanes, bk=bk,
                ebig=ebig, elev=elev, okS=okS)


def np_nonzero(s):
    import numpy as np
    return np.nonzero(s)[0].tolist()


def L(x):
    if x < (1 << 16384):
        return f'0x{x:x}'
    return 'bignat% [' + ', '.join(BS.chunks_of_big(x)) + ']'


def mask_expr(syms):
    e = 'full'
    for s in syms:
        if s[0] == 'skip':
            e = f'Nat.land ({e}) (m {s[1]} 1)'
        elif s[0] == 'push':
            e = f'Nat.land ({e}) (Nat.lor (m {s[1]} 2) (m {s[1]} 3))'
        elif s[0] == 'pop0':
            e = f'Nat.land ({e}) (Nat.lor (Nat.land (m {s[1]} 2) (m {s[2]} 2)) (Nat.land (m {s[1]} 3) (m {s[2]} 3)))'
        else:
            e = f'Nat.land ({e}) (Nat.lor (Nat.land (m {s[1]} 2) (m {s[2]} 3)) (Nat.land (m {s[1]} 3) (m {s[2]} 2)))'
    return e


def cert_expr(syms):
    e = 'certMask'
    for s in syms:
        if s[0] in ('pop0', 'pop1'):
            e = f'Nat.xor ({e}) (Nat.land ({e}) (okf {s[2]} {s[1]}))'
    return e


def emit(idx, D, outdir):
    n, N, col, certmask, exact, lower, maxr = D['n'], D['N'], D['col'], D['certmask'], D['exact'], D['lower'], D['maxr']
    okS = D['okS']
    full = (1 << N) - 1

    def mm(p, c):
        return col[(p, str(c))]

    # ---- simulate the walk: node counts of the subtrees at the split points ----
    sys.setrecursionlimit(10000)
    counts = {}

    def count(d, syms, stack, a, c):
        if a & c == 0:
            cnt = 1
        elif d == n:
            cnt = 1
        else:
            cnt = 1
            cnt += count(d + 1, syms + [('skip', d)], stack, a & mm(d, 1), c)
            cnt += count(d + 1, syms + [('push', d)], stack + [d], a & (mm(d, 2) | mm(d, 3)), c)
            if stack:
                q = stack[-1]
                c2 = c ^ (c & okS[(q, d)])
                cnt += count(d + 1, syms + [('pop0', d, q)], stack[:-1],
                             a & ((mm(d, 2) & mm(q, 2)) | (mm(d, 3) & mm(q, 3))), c2)
                cnt += count(d + 1, syms + [('pop1', d, q)], stack[:-1],
                             a & ((mm(d, 2) & mm(q, 3)) | (mm(d, 3) & mm(q, 2))), c2)
        if d <= DMAX:
            counts[tuple(syms)] = cnt
        return cnt

    total = count(0, [], [], full, certmask)
    leaf_nodes = max(200, min(LEAF_NODES_MAX, LEAF_BYTES // (4 * (N // 8 + 1))))

    # ---- the tree of theorems ----
    lines, counter = [], [0]

    def emit_node(syms, stack, d):
        name = f'part{counter[0]}'; counter[0] += 1
        expr, cexpr = mask_expr(syms), cert_expr(syms)
        st = '[' + ', '.join(str(x) for x in reversed(stack)) + ']'
        cnt = counts[tuple(syms)]
        if cnt <= leaf_nodes or d == DMAX or d == n:
            lines.append(
                f'set_option maxHeartbeats 0 in\n'
                f'/-- Subtree below `{"/".join(x[0] for x in syms) or "ε"}` ({cnt} nodes). -/\n'
                f'theorem {name} : walk {n - d} {d} {st} ({expr}) ({cexpr}) = true := by\n'
                f'  decide +kernel\n')
            return name
        kids = [emit_node(syms + [('skip', d)], stack, d + 1),
                emit_node(syms + [('push', d)], stack + [d], d + 1)]
        if stack:
            kids.append(emit_node(syms + [('pop0', d, stack[-1])], stack[:-1], d + 1))
            kids.append(emit_node(syms + [('pop1', d, stack[-1])], stack[:-1], d + 1))
        lines.append(
            f'/-- Glues the subtrees below `{"/".join(x[0] for x in syms) or "ε"}`. -/\n'
            f'theorem {name} : walk {n - d} {d} {st} ({expr}) ({cexpr}) = true := by\n'
            f'  rw [walk]\n'
            f'  rw [ite_eq_right (by decide : ¬((Nat.land ({expr}) ({cexpr}) == 0) = true))]\n'
            f'  rw [{", ".join(kids)}]\n'
            f'  rfl\n')
        return name

    root = emit_node([], [], 0)
    parts = NL.join(lines)
    rows = NL.join(
        f'/-- The traces with colour `c{c}` at each position. -/\n'
        f'def col{c} : Nat → Nat\n' +
        NL.join(f'  | {p} => {L(col[(p, str(c))])}' for p in range(n)) + '\n  | _ => 0\n'
        for c in (1, 2, 3))
    okrows = NL.join(
        f'/-- The certified traces the chords `({q}, p)` settle. -/\n'
        f'def ok{q} : Nat → Nat\n' +
        NL.join(f'  | {p} => {L(okS[(q, p)])}' for p in range(q + 1, n)) + '\n  | _ => 0\n'
        for q in range(n - 1))
    okmatch = NL.join(f'  | {q} => ok{q} p' for q in range(n - 1))
    pairs = ', '.join(f'({L(exact[r])}, {L(lower[r])})' for r in range(maxr + 1))
    src = f'''/-
Chord-aware mask certificate for configuration {idx} (ring {n}).

{N} traces in the universe: the {bin(certmask).count("1")} the certificate is
responsible for, plus the witnesses the walk needs.  The walk carries a mask
over them and the certified set still to justify; a closed chord removes what
it settles, and the leaf test asks whether a witness ranks below the lowest
rank present.  {total} nodes, in {counter[0]} declarations.

Generated by `scripts/gen_maskc_jobs.py`.
-/
import FourColor.MaskRank
import FourColor.Bulk.Lit
set_option Elab.async false

namespace FourColor
namespace Cfg{idx:03d}

def n : Nat := {n}
def width : Nat := {N}

{rows}
def certMask : Nat := {L(certmask)}
/-- `(traces of exactly rank r, witnesses below rank r)`, lowest rank first. -/
def rankPairs : RankPairs := [{pairs}]

{okrows}
/-- The mask of colour `c` at position `p`. -/
def m (p c : Nat) : Nat :=
  match c with
  | 1 => col1 p
  | 2 => col2 p
  | 3 => col3 p
  | _ => 0

/-- The certified traces the chord `(q, p)` settles. -/
def okf (q p : Nat) : Nat :=
  match q with
{okmatch}
  | _ => 0

@[inline] def leafOk (c a : Nat) : Bool :=
  let A := Nat.land a c
  A == 0 || firstRank rankPairs A a

def walk : Nat → Nat → List Nat → Nat → Nat → Bool
  | 0,        _, stack, a, c => !stack.isEmpty || leafOk c a
  | fuel + 1, p, stack, a, c =>
    if Nat.land a c == 0 then true else
      walk fuel (p+1) stack (Nat.land a (m p 1)) c
      &&
      walk fuel (p+1) (p :: stack) (Nat.land a (Nat.lor (m p 2) (m p 3))) c
      &&
      (match stack with
       | [] => true
       | q :: rest =>
         walk fuel (p+1) rest
           (Nat.land a (Nat.lor (Nat.land (m p 2) (m q 2)) (Nat.land (m p 3) (m q 3))))
           (Nat.xor c (Nat.land c (okf q p)))
         &&
         walk fuel (p+1) rest
           (Nat.land a (Nat.lor (Nat.land (m p 2) (m q 3)) (Nat.land (m p 3) (m q 2))))
           (Nat.xor c (Nat.land c (okf q p))))

def full : Nat := Nat.shiftLeft 1 width - 1

{parts}
/-- **Every chromogram reached by a certified trace, that no chord settles, has
a witness below the lowest rank present.** -/
theorem covered : walk n 0 [] full certMask = true := {root}

end Cfg{idx:03d}
end FourColor
'''
    os.makedirs(outdir, exist_ok=True)
    open(os.path.join(outdir, f'Cfg{idx:03d}.lean'), 'w').write(src)
    return total, counter[0]


if __name__ == '__main__':
    planesdir, gendir, certdir, outdir = sys.argv[1:5]
    for i in [int(x) for x in sys.argv[5:]]:
        D = build_all(i, planesdir, gendir, certdir)
        total, ndecl = emit(i, D, outdir)
        print(f'cfg{i:03d}: ring={D["n"]} universe={D["N"]} entries={len(D["entries"])} '
              f'nodes={total} decls={ndecl}')

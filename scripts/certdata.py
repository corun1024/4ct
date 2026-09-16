#!/usr/bin/env python3
"""Reading a residual certificate and building the walk's universe.

Shared by `gen_maskc_jobs.py` (the walk module) and `gen_hybt_jobs.py` (the
bridge module).  A certificate file (`k14.c`'s output) lists, per entry, its
complete trace, its rank and its answers: flip masks over the trace naming a
witness, either free (`G`, a trace the bulk certificate knows) or justified by
a colour permutation into a lower-ranked entry (`P`).
"""
import os

# the six colour permutations, on the digits `1`, `2`, `3`
PERMS = [{'1': '1', '2': '2', '3': '3'}, {'1': '1', '2': '3', '3': '2'}, {'1': '2', '2': '1', '3': '3'}, {'1': '2', '2': '3', '3': '1'}, {'1': '3', '2': '1', '3': '2'}, {'1': '3', '2': '2', '3': '1'}]
PERM_NAMES = ['e123', 'e132', 'e213', 'e231', 'e312', 'e321']


def read_cert(path):
    ring, entries = None, []
    for line in open(path):
        f = line.split()
        if not f: continue
        if f[0] == 'ring':
            ring = int(f[1]); continue
        if f[0] != 'E': continue
        trace, rank, nans = f[1], int(f[2]), int(f[3])
        i, ans = 4, []
        for _ in range(nans):
            if f[i] == 'G': ans.append(('G', int(f[i+1]), None)); i += 2
            else:           ans.append(('P', int(f[i+1]), int(f[i+2]))); i += 3
        entries.append((trace, rank, ans))
    return ring, entries


def flip(part, mask):
    return ''.join(('3' if c == '2' else '2' if c == '3' else c) if (mask >> i) & 1 else c
                   for i, c in enumerate(part))


def complete(part):
    s = 0
    for c in part: s ^= int(c)
    return part + str(s)


def build_wit_entries(idx, ring, entries):
    """`build_wit` on an already-read certificate `(ring, entries)`."""
    n = ring
    rank_of = {t: r for t, r, _ in entries}
    universe = [t for t, _, _ in entries]
    seen = set(universe)
    good = set()
    permrank = {}          # witness -> (rank, perm index) achieving the minimum
    for trace, rank, ans in entries:
        for kind, mask, pk in ans:
            v = complete(flip(trace[:-1], mask))
            if v not in seen:
                seen.add(v); universe.append(v)
            if kind == 'G':
                good.add(v)
            else:
                tgt = ''.join(PERMS[pk][c] for c in v)
                r = rank_of.get(tgt)
                if r is not None and r < permrank.get(v, (10 ** 9, 0))[0]:
                    permrank[v] = (r, pk)
    N = len(universe)
    pos = {t: i for i, t in enumerate(universe)}
    col = {}
    for p in range(n):
        for c in '123':
            v = 0
            for i, t in enumerate(universe):
                if t[p] == c: v |= (1 << i)
            col[(p, c)] = v
    certmask = 0
    for t, _, _ in entries: certmask |= (1 << pos[t])
    maxr = max(r for _, r, _ in entries)
    exact = [0] * (maxr + 1)
    for t, r, _ in entries: exact[r] |= (1 << pos[t])
    goodmask = 0
    for v in good: goodmask |= (1 << pos[v])
    # the witness levels: at level r, the witnesses whose smallest certified
    # permutation sits at rank exactly r, split by which permutation that is
    wl = [dict() for _ in range(maxr + 1)]
    for v, (r, pk) in permrank.items():
        wl[r][pk] = wl[r].get(pk, 0) | (1 << pos[v])
    # `lower`, exactly as the walk's numerals were built, must be what
    # `buildRank` computes from `goodmask` and `wl`
    lower = []
    acc = goodmask
    for r in range(maxr + 1):
        lower.append(acc)
        for pk in sorted(wl[r]): acc |= wl[r][pk]
    chk = []
    for r in range(maxr + 1):
        m = goodmask
        for v, (vr, _) in permrank.items():
            if vr < r: m |= (1 << pos[v])
        chk.append(m)
    assert chk == lower, f"cfg{idx}: buildRank disagrees with the emitted rank masks"
    goods = sorted(good)
    return n, N, col, certmask, exact, lower, maxr, goodmask, wl, goods, universe


def build_wit(idx, certdir):
    """The same universe `gen_mask_jobs` builds, plus the witness levels."""
    ring, entries = read_cert(os.path.join(certdir, f'{idx}.txt'))
    return build_wit_entries(idx, ring, entries)


def M_lit(x):
    """A numeral, chunked when wide."""
    if x < (1 << 16384):
        return f'0x{x:x}'
    chunks = []
    while x:
        chunks.append(f'0x{x & ((1 << 16384) - 1):x}')
        x >>= 16384
    return 'bignat% [' + ', '.join(chunks) + ']'


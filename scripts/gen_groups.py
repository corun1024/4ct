#!/usr/bin/env python3
"""Partition the bulk configurations into the groups that share a module.

A bulk module costs a few seconds of fixed overhead (imports, elaboration)
before its first kernel computation, so bulk configurations are packed several
to a module (`gen_bulk_jobs.py --group`).  The kernel work of a configuration is
dominated by operations on 3^(ring-1)-bit numbers, so the groups are cut by
ring size: sorted by ring size, consecutive configurations of one ring size
share a group, K to a group with K = 4 for ring 14, 8 for ring 13, 16 for ring
12 and 32 below, and a group never crosses ring sizes.  Group `Grp<ring>_<k>`
is the k-th group (from 0) of that ring size.

Usage: gen_groups.py <hybrid-index-file> [--size K] [--gen <gendir>] [--out <path>]
                     [--total N]

`<hybrid-index-file>` lists the indices the bulk rule does not settle; every
other index below `--total` (default 633) is a bulk configuration.  `--size K`
overrides the ring-size table with a single K.  `--gen` is the directory of the
`<idx>.in` inputs, whose first line is `ring <n>` (default `$S/gen` for the
scratchpad `S`, else `gen`).  One line `<name> <idx>...` is printed per group and
the same lines are written to `--out` (default `$S/groups.txt`, else `groups.txt`).
"""
import os
import sys

SIZE_BY_RING = {14: 4, 13: 8, 12: 16}
SIZE_DEFAULT = 32


def group_size(ring, override=None):
    if override is not None:
        return override
    return SIZE_BY_RING.get(ring, SIZE_DEFAULT)


def ring_of(gendir, i):
    with open(os.path.join(gendir, f'{i}.in')) as f:
        return int(f.readline().split()[1])


def groups(bulk, rings, override=None):
    """`[(name, [idx, ...]), ...]` for the bulk indices `bulk` with ring sizes `rings`."""
    out = []
    by_ring = {}
    for i in sorted(bulk, key=lambda i: (rings[i], i)):
        by_ring.setdefault(rings[i], []).append(i)
    for ring in sorted(by_ring):
        k = group_size(ring, override)
        idxs = by_ring[ring]
        for g, start in enumerate(range(0, len(idxs), k)):
            out.append((f'Grp{ring:02d}_{g:02d}', idxs[start:start + k]))
    return out


if __name__ == '__main__':
    args = sys.argv[1:]
    S = os.environ.get('S')
    gendir = os.path.join(S, 'gen') if S else 'gen'
    outpath = os.path.join(S, 'groups.txt') if S else 'groups.txt'
    total, override, hybfile = 633, None, None
    while args:
        a = args.pop(0)
        if a == '--size':
            override = int(args.pop(0))
        elif a == '--gen':
            gendir = args.pop(0)
        elif a == '--out':
            outpath = args.pop(0)
        elif a == '--total':
            total = int(args.pop(0))
        else:
            hybfile = a
    if hybfile is None:
        sys.exit(__doc__)
    hyb = set(int(x) for x in open(hybfile).read().split())
    bulk = [i for i in range(total) if i not in hyb]
    rings = {i: ring_of(gendir, i) for i in bulk}
    lines = [f'{name} ' + ' '.join(str(i) for i in idxs) for name, idxs in groups(bulk, rings, override)]
    print('\n'.join(lines))
    with open(outpath, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(f'{len(lines)} groups for {len(bulk)} bulk configurations -> {outpath}', file=sys.stderr)

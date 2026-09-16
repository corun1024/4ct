#!/usr/bin/env python3
"""Bulk-space data for a residual configuration.

The bulk universe indexes a trace by its first `m` colours as base-3 digits.
This builds, with numpy over all `3^m` indices:

  * `K`      — the traces the bulk certificate knows (`knownMask` in Lean:
               the permutation closure of the certified ones);
  * `R'`     — rank planes for the residual walk: rank 0 on `K`, `r + 1` on
               the entries of level `r`, the top rank elsewhere;
  * `H'`     — `minPerm` of `R'`: the smallest rank among a trace's colour
               permutations;
  * `ok`     — for every chord `(q, p)`, the entries one of whose three flips
               along it is known or permutes to an entry of smaller level
               (`okBig` in Lean, restricted to the entries).
"""
import numpy as np

# the six colour permutations on digits 0..2 (colour = digit + 1)
PERM6 = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]


def big_of_chunks(chunks):
    x = 0
    for k, c in enumerate(chunks):
        x |= int(c, 16) << (16384 * k)
    return x


def chunks_of_big(x):
    if x == 0:
        return ['0x0']
    out = []
    while x:
        out.append(f'0x{x & ((1 << 16384) - 1):x}')
        x >>= 16384
    return out


def bits_of_big(x, N):
    b = x.to_bytes((N + 7) // 8, 'little')
    return np.unpackbits(np.frombuffer(b, dtype=np.uint8), bitorder='little')[:N].astype(bool)


def big_of_bits(bits):
    return int.from_bytes(np.packbits(bits, bitorder='little').tobytes(), 'little')


class Bulk:
    def __init__(self, m):
        self.m = m
        self.N = N = 3 ** m
        idx = np.arange(N, dtype=np.int64)
        self.digits = np.stack([(idx // 3 ** p) % 3 for p in range(m)], axis=1)  # N x m
        self.permidx = []
        for g in PERM6:
            gmap = np.array(g, dtype=np.int64)
            j = np.zeros(N, dtype=np.int64)
            for p in range(m):
                j += gmap[self.digits[:, p]] * 3 ** p
            self.permidx.append(j)

    def val_of_planes(self, planes):
        v = np.zeros(self.N, dtype=np.int64)
        for b, pl in enumerate(planes):
            v |= bits_of_big(pl, self.N).astype(np.int64) << b
        return v

    def planes_of_val(self, v, nplanes):
        return [big_of_bits(((v >> b) & 1).astype(bool)) for b in range(nplanes)]

    def perm_close(self, bits):
        out = bits.copy()
        for pi in self.permidx:
            out |= bits[pi]
        return out

    def min_perm(self, v):
        out = v.copy()
        for pi in self.permidx:
            out = np.minimum(out, v[pi])
        return out

    def known(self, R):
        """`knownMask m R`: some permutation is certified (rank below the top)."""
        v = self.val_of_planes(R)
        top = (1 << len(R)) - 1
        return self.perm_close(v != top)

    def residual_planes(self, Kb, entries_big, entries_level, maxr):
        """`R'` and `H'` (as values), and the number of planes."""
        nplanes = max(2, (maxr + 3).bit_length())
        top = (1 << nplanes) - 1
        v = np.full(self.N, top, dtype=np.int64)
        v[Kb] = 0
        v[np.asarray(entries_big, dtype=np.int64)] = np.asarray(entries_level, dtype=np.int64) + 1
        return v, self.min_perm(v), nplanes

    def settled(self, valR, valH, entries_big, entries_level, n):
        """For every chord `(q, p)`, the boolean array of settled entries."""
        m = self.m
        eb = np.asarray(entries_big, dtype=np.int64)
        lv = np.asarray(entries_level, dtype=np.int64)
        d = self.digits[eb]                                  # entries x m, digits 0..2
        comp = np.bitwise_xor.reduce(d + 1, axis=1)          # completing colour 1..3 (0 impossible)
        dfull = np.concatenate([d, (comp - 1)[:, None]], axis=1)   # entries x n
        delta = np.where(d == 1, 1, -1) * (3 ** np.arange(m))[None, :]   # flip 2<->3 at stored digit
        delta = np.where(d == 0, 0, delta)
        deltaf = np.concatenate([delta, np.zeros((len(eb), 1), dtype=np.int64)], axis=1)
        out = {}
        for q in range(n):
            for p in range(q + 1, n):
                okq = (dfull[:, q] != 0) & (dfull[:, p] != 0)
                inside = dfull[:, q + 1:p] != 0
                even = (inside.sum(axis=1) % 2) == 0
                valid = okq & even
                ic = deltaf[:, q] + deltaf[:, p]
                ia = (deltaf[:, q + 1:p] * inside).sum(axis=1) if p > q + 1 else np.zeros(len(eb), dtype=np.int64)
                s = np.zeros(len(eb), dtype=bool)
                for cand in (eb + ic, eb + ia, eb + ic + ia):
                    cand = np.where(valid, cand, 0)
                    s |= valid & (valH[cand] < lv + 1)
                out[(q, p)] = s
        return out


def big_index(trace, m):
    """Bulk index of a complete trace string."""
    return sum((int(trace[p]) - 1) * 3 ** p for p in range(m))

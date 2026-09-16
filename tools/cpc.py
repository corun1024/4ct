#!/usr/bin/env python3
"""Independent port of FourColor's cpcolor / cfctr, as set transformers.
Colours: 0..3 with XOR as Klein addition (c1=1,c2=2,c3=3)."""
import re, sys, os

def e231(c): return {0:0,1:2,2:3,3:1}[c]
def e312(c): return {0:0,1:3,2:1,3:2}[c]
def e132(c): return {0:0,1:1,2:3,3:2}[c]
def rotTo(c):  # perm sending c to c1
    return {0:(lambda x:x),1:(lambda x:x),2:e312,3:e231}[c]

def rotate(l, k):
    if not l: return l
    k %= len(l); return l[k:] + l[:k]

def step(s, et):
    """cpcolor1 s: one trace -> list of traces (the enumeration)."""
    if s[0] == 'R':
        return [rotate(et, s[1])]
    if s[0] == "R'":
        return [] if len(et) <= 1 else [rotate(et, len(et)-1)]
    if s[0] == 'U':
        return [(1,1)+et, (2,2)+et, (3,3)+et]
    if s[0] == 'Y':
        if not et: return []
        e1, r = et[0], et[1:]
        return [(e231(e1), e312(e1)) + r, (e312(e1), e231(e1)) + r]
    if s[0] == 'K':
        if len(et) < 2: return []
        e1, e2, r = et[0], et[1], et[2:]
        return [] if e1 == e2 else [(e1 ^ e2,) + r]
    if s[0] == 'H':
        if len(et) < 2: return []
        e1, e2, r = et[0], et[1], et[2:]
        if e1 == e2: return [(e231(e1), e231(e1)) + r, (e312(e1), e312(e1)) + r]
        return [(e2, e1) + r]
    if s[0] == 'A':
        if len(et) < 2: return []
        e1, e2, r = et[0], et[1], et[2:]
        if e1 != e2: return []
        return [r if r else (e1, e2)]
    raise ValueError(s)

def fold(steps, base):
    """foldr cpcolor1 cpbranch steps base : the set of final traces (before cpbranch)."""
    cur = {tuple(base)}
    for s in steps:
        nxt = set()
        for et in cur:
            for e in step(s, et): nxt.add(e)
        cur = nxt
    return cur

def cpcolor0(cp):
    """cp is already reversed. Returns set of final traces."""
    if cp and cp[0][0] == 'R': return cpcolor0(cp[1:])
    if cp and cp[0][0] == 'Y': return fold(cp[1:], [1,2,3])
    if cp and cp[0][0] == 'U': return fold(cp[1:], [1,1,2,2]) | fold(cp[1:], [1,1,1,1])
    return fold(cp, [1,1])

def evenize(l):
    for c in l:
        if c == 2: return tuple(l)
        if c == 3: return tuple(e132(x) for x in l)
    return tuple(l)

def cpbranch_key(et):
    """cpbranch et = ofTrace (evenNormTail et.tail); return the stored inner key, or None."""
    if len(et) < 2: return None
    e, rest = et[1], et[2:]
    if e == 0: return None
    g = rotTo(e)
    return evenize([g(x) for x in rest])

def cpcolor_stored(cp):
    """The traces `enumC (cpcolor cp)` lists: partial traces pt of length n-1 with
    mem (consRot t) pt = mem t (normTail pt), t the inner tree.  Inner keys have
    length n-2; pt = c :: rest with normTail pt = rest.map(rotTo c) in t.
    We return the set of pt (as digit strings)."""
    fin = cpcolor0(list(reversed(cp)))
    inner = set()
    for et in fin:
        k = cpbranch_key(et)
        if k is not None: inner.add(k)
    # rotl/rotr children: mem (cons t (rotl t) (rotr t)) (c :: rest) =
    #   c1 -> mem t rest ; c2 -> mem (rotl t) rest ; c3 -> mem (rotr t) rest
    # and mem (consRot t) pt = mem t (normTail pt) = mem t (rest.map (rotTo c)).
    out = set()
    inv = {1:(lambda x:x), 2:e231, 3:e312}   # inverse of rotTo c
    for key in inner:
        for c in (1,2,3):
            rest = tuple(inv[c](x) for x in key)
            out.add(''.join(str(x) for x in (c,)+rest))
    return out

# ---- contracts ----
def ctrmsize(cp):
    if not cp: return 0
    s = cp[0]
    if s[0] == 'R': return ctrmsize(cp[1:])
    if s[0] == 'Y': return 0 if len(cp) == 1 else ctrmsize(cp[1:]) + 1
    if s[0] == 'H': return ctrmsize(cp[1:]) + 3
    return 0

def cprsize(cp):
    if not cp: return 2
    s = cp[0]; r = cprsize(cp[1:])
    if s[0] in ('R', "R'", 'H'): return r
    if s[0] == 'Y': return r + 1
    if s[0] == 'U': return r + 2
    if s[0] == 'K': return r - 2 + 1
    if s[0] == 'A': return r - 2 if r > 2 else r
    raise ValueError(s)

def notSparse(b1, b2, b3): return (b2 or b3) if b1 else (b2 and b3)

def rotrMask(n, m):
    if not m: return m
    return rotate(m, len(m) - n % len(m))

def cfctr(cp, mr, mc):
    if not cp: return None
    s = cp[0]
    if s[0] == 'R':
        i = s[1]; mr2 = rotrMask(i, mr)
        r = cfctr(cp[1:], mr2, mc)
        if r is None: return None
        cnt = sum(1 for b in mr2[: (i % len(mr)) if mr else 0] if not b)
        return [('R', cnt)] + r
    if s[0] == 'Y' and len(cp) == 1:
        if len(mr) < 3: return None
        b1, b2, b3 = mr[0], mr[1], mr[2]
        if notSparse(b1, b2, b3): return None
        return [] if (b1 or b2 or b3) else [('Y',)]
    if s[0] == 'Y':
        if len(mr) < 2 or len(mc) < 1: return None
        b1, b2, mr2 = mr[0], mr[1], mr[2:]
        b3, mc2 = mc[0], mc[1:]
        if notSparse(b1, b2, b3): return None
        r = cfctr(cp[1:], [b3] + mr2, mc2)
        if r is None: return None
        if b1 or b2: return r
        return [('U',) if b3 else ('Y',)] + r
    if s[0] == 'H':
        if len(mr) < 2 or len(mc) < 3: return None
        b1, b2, mr2 = mr[0], mr[1], mr[2:]
        b3, b4, b5, mc2 = mc[0], mc[1], mc[2], mc[3:]
        if notSparse(b3, b1, b4) or notSparse(b3, b2, b5): return None
        if b1 and b2 and all(mr2): return None
        r = cfctr(cp[1:], [b4, b5] + mr2, mc2)
        if r is None: return None
        if b3: return r
        if b1: return ([('A',)] + r) if b2 else (r if b5 else [('K',)] + r)
        if b2: return r if b4 else [('K',)] + r
        if b4: return [('U',) if b5 else ('Y',)] + r
        return [('Y',) if b5 else ('H',)] + r
    return None

def contract_prog(cf):
    sym, cci, prog = cf
    n = cprsize(prog)
    mask = [i in cci for i in range(ctrmsize(prog))]
    return cfctr(prog, [False]*n, mask)

# ---- parse Configurations.lean ----
def parse_configs(path):
    txt = open(path).read()
    cfs = []
    for m in re.finditer(r'def cf(\d+) : Config :=\s*⟨(true|false), \[([^\]]*)\], \[([^\]]*)\]⟩', txt):
        idx = int(m.group(1)); sym = m.group(2) == 'true'
        cci = [int(x) for x in m.group(3).split(',') if x.strip()]
        steps = []
        for tok in re.findall(r'\.(H|Y|U|K|A|R\'|R \d+)', m.group(4)):
            if tok.startswith('R '): steps.append(('R', int(tok[2:])))
            else: steps.append((tok,))
        cfs.append((idx, (sym, cci, steps)))
    cfs.sort()
    return [c for _, c in cfs]

if __name__ == '__main__':
    cfs = parse_configs(sys.argv[1])
    print(len(cfs), 'configs')
    which = [int(x) for x in sys.argv[3:]] if len(sys.argv) > 3 else range(len(cfs))
    outdir = sys.argv[2]; os.makedirs(outdir, exist_ok=True)
    for i in which:
        cf = cfs[i]
        n = cprsize(cf[2])
        good = cpcolor_stored(cf[2])
        cpc = contract_prog(cf)
        ctr = cpcolor_stored(cpc) if cpc is not None else set()
        with open(f'{outdir}/{i}.in', 'w') as f:
            f.write(f'ring {n}\n')
            f.write('GOOD ' + ' '.join(sorted(good)) + '\n')
            f.write('CTR ' + ' '.join(sorted(ctr)) + '\n')
        print(f'CFG {i} ring {n} good {len(good)} ctr {len(ctr)}', flush=True)

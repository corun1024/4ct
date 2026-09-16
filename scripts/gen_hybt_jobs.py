#!/usr/bin/env python3
"""Generate the table-based hybrid reducibility module(s) of a configuration.

The bridge between the bulk certificate (`gen_bulk_jobs.py`) and the
chord-aware mask walk (`gen_maskc_jobs.py`, in `FourColor/Mask/Cfg<idx>.lean`):
the bulk planes and their checks, the small universe's `Masks`, the witness
levels, the entries by level, the packed index table, the residual rank planes
`R'`/`H'` over the bulk universe, the per-chord settling checks, and
`Bulk.cfReducible_of_hybridT`.

A configuration with few entries gets one module, `FourColor/Bulk/Cfg/Hyb<idx>.lean`.
A large one is split so that its checks build in parallel: the data in
`Hyb<idx>D.lean`, the checks in `Hyb<idx>A.lean` (bulk pairs), `Hyb<idx>B.lean`
(table, entries, contract), `Hyb<idx>C.lean` (levels and witnesses),
`Hyb<idx>K<i>.lean` (chord settling, several parts), and the assembly in
`Hyb<idx>.lean`, which is what `gen_all.py` imports either way.

Usage: scripts/gen_hybt_jobs.py <planesdir> <gendir> <certdir> <outdir> [--split|--single] <idx>...
"""
import os
import sys

SEP = ",\n  "
SEP2 = "\n  "
NL = "\n"

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_bulk_jobs as B
import certdata as Hy
import gen_maskc_jobs as MC
import bulkspace as BS

PERM_NAMES = Hy.PERM_NAMES
PAIR_GROUP = 8         # pair checks per declaration (the witness planes are recomputed per declaration)
FREE_CHUNK = 1000      # small-universe indices per free-witness declaration
E_CHUNK = 500          # entries per declaration
SPLIT_ENTRIES = 3000   # split the module above this many entries
OK_PARTS = 3           # chord-settling parts of a split module

HEADER = ''


def module(name, imports, doc, body):
    """One Lean module: header, imports, docstring, options, namespace, body."""
    return (HEADER + NL.join(f'import {i}' for i in imports) + '\n\n/-!\n' + doc + '-/\n\n'
            'set_option Elab.async false\nset_option maxRecDepth 100000\n\n'
            f'namespace FourColor\nnamespace Bulk\nnamespace {name}\n\nopen FourColor.Masks\n\n'
            + NL.join(body) + f'\nend {name}\nend Bulk\nend FourColor\n')


def emit(idx, D, outdir, split=None):
    n, m, N = D['n'], D['m'], D['N']
    P = D['P']
    Rchunks = D['Rchunks']
    Cchunks = [P[f'choice{b}'] for b in range(4)]
    certmask, exact, maxr, goodmask, wl = D['certmask'], D['exact'], D['maxr'], D['goodmask'], D['wl']
    entries, ebig, elev = D['entries'], D['ebig'], D['elev']
    bk, valR, nplanes = D['bk'], D['valR'], D['nplanes']
    Rp = bk.planes_of_val(valR, nplanes)
    nlev = maxr + 1
    EL = [[(i, ebig[i]) for i in range(len(entries)) if elev[i] == r] for r in range(nlev)]
    pairs = [(p, q) for q in range(n) for p in range(q)]
    M_lit = Hy.M_lit
    universe = D['universe']
    Tpacked = 0
    for j, t in enumerate(universe):
        Tpacked |= BS.big_index(t, m) << (32 * j)
    Lbits = max(1, (N - 1).bit_length())
    npieces = (N + 8191) // 8192
    okS = D['okS']
    if split is None:
        split = len(entries) >= SPLIT_ENTRIES
    hyb = f'Hyb{idx:03d}'
    cfg = f'Cfg{idx:03d}'

    def packed_idx(js):
        packed = 0
        for t, j in enumerate(js):
            assert j < (1 << 18)
            packed |= j << (18 * t)
        return f'unpackIdx ({M_lit(packed)}) {len(js)}'

    wlL_items = []
    for r in range(nlev):
        parts = []
        for pk in sorted(wl[r]):
            js = [j for j in range(N) if (wl[r][pk] >> j) & 1]
            parts.append(f'(EdgePerm.{PERM_NAMES[pk]}, {packed_idx(js)})')
        wlL_items.append(f'  ({M_lit(exact[r])}, [{", ".join(parts)}])')
    wlL_rows = ',\n'.join(wlL_items)
    settled = {(q, p): [j for j in range(len(entries)) if (okS[(q, p)] >> j) & 1] for (q, p) in okS}

    # ---------------- the data ----------------
    defs = []
    defs.append(f'''/-- The configuration. -/
def cf : Config := theConfigs[{idx}]!

/-- The number of stored digits. -/
def dm : ℕ := {m}

def R : List ℕ := [
  {SEP.join(B.lit(r) for r in Rchunks)}]

/-- Witness planes: the least rank among the six colour permutations of each trace. -/
def H : List ℕ := minPerm dm R

def C : List ℕ := [
  {SEP.join(B.lit(c) for c in Cchunks)}]

theorem hcf : cprsize cf.prog = dm + 1 := by decide +kernel

theorem hH : H = minPerm dm R := rfl

/-! ### The residual walk -/

/-- The small universe's masks. -/
def ms : Masks := ⟨{cfg}.n, {cfg}.width, fun p c => {cfg}.m p (colourCode c)⟩

/-- The free witnesses of the residual certificate. -/
def goodMask : ℕ := {M_lit(goodmask)}

/-- The witness levels: at level `r`, for each permutation, the witnesses (by index)
whose image under it is an entry of level `r`. -/
def wlL : List (ℕ × List (EdgePerm × List ℕ)) := [
{wlL_rows}
]

/-- The witness levels as masks. -/
def wl : List (ℕ × List (EdgePerm × ℕ)) := wlOf ms wlL

/-- Lane `j` of the table: the bulk index of trace `j`, thirty-two bits each. -/
def T : ℕ := {M_lit(Tpacked)}

/-- `2^L` bounds the universe. -/
def L : ℕ := {Lbits}

/-- The table in pieces. -/
def P : List ℕ := lanePieces T {npieces}

theorem hlen : ms.len = dm + 1 := by decide

theorem walk_eq : ∀ fuel p stack a c,
    {cfg}.walk fuel p stack a c =
      ms.walkCF {cfg}.okf {cfg}.rankPairs fuel p stack a c := by
  intro fuel
  induction fuel with
  | zero => intro p stack a c; rfl
  | succ fuel ih => intro p stack a c; simp only [{cfg}.walk, Masks.walkCF, ih]; rfl

theorem hwalk : ms.walkC {cfg}.okf {cfg}.rankPairs
    (List.range ms.len) [] ms.full {cfg}.certMask = true := by
  have hf : ms.full = {cfg}.full := full_eq_shiftLeft ms
  change ms.walkC {cfg}.okf {cfg}.rankPairs
    (List.range {cfg}.n) [] ms.full {cfg}.certMask = true
  rw [hf, List.range_eq_range', ← ms.walkCF_eq]
  exact (walk_eq {cfg}.n 0 [] {cfg}.full {cfg}.certMask).symm.trans
    {cfg}.covered

/-! ### The entries, by level -/
''')
    chunk_names = []
    for r in range(nlev):
        ch = [EL[r][i:i + E_CHUNK] for i in range(0, len(EL[r]), E_CHUNK)]
        names = []
        for k, c in enumerate(ch):
            packed = 0
            for t, (j, big) in enumerate(c):
                assert j < (1 << 18) and big < (1 << 22)
                packed |= ((big << 18) | j) << (40 * t)
            defs.append(f'''/-- Level {r}, entries {k * E_CHUNK} to {k * E_CHUNK + len(c) - 1}, packed. -/
def E_{r}_{k} : List (ℕ × ℕ) := unpackE ({M_lit(packed)}) {len(c)}
''')
            names.append(f'E_{r}_{k}')
        chunk_names += names
        defs.append(f'''/-- The entries of level {r}. -/
def E_{r} : List (ℕ × ℕ) := {" ++ ".join(names) if names else "[]"}
''')
    defs.append(f'''/-- The entries, by level. -/
def EL : List (List (ℕ × ℕ)) := [{", ".join(f"E_{r}" for r in range(nlev))}]

/-- All entries. -/
def E : List (ℕ × ℕ) := EL.flatten

/-! ### The residual rank planes -/

def R' : List ℕ := [
  {SEP.join(B.lit(BS.chunks_of_big(x)) for x in Rp)}]

/-- The residual witness planes. -/
def H' : List ℕ := minPerm dm R'

theorem hH' : H' = minPerm dm R' := rfl

theorem htop : wl.length + 1 < rankTop R' := by decide +kernel

/-! ### What each chord settles -/
''')
    for (q, p) in pairs:
        defs.append(f'''/-- The entries chord `({q}, {p})` settles. -/
def S_{q}_{p} : List ℕ := {packed_idx(settled[(q, p)])}
''')
    smatch = NL.join(
        f"  | {q} => match p with\n" + NL.join(f"    | {p} => S_{q}_{p}" for p in range(q + 1, n)) +
        "\n    | _ => []" for q in range(n - 1))
    defs.append(f'''/-- The settled entries of every chord. -/
def Sf (q p : ℕ) : List ℕ :=
  match q with
{smatch}
  | _ => []
''')

    # ---------------- the bulk checks ----------------
    chk_bulk = [f'''theorem hgood : goodCheck dm R cf.prog = true := by decide +kernel

theorem hchoice : choiceCheck dm R C = true := by decide +kernel
''']
    groups = [pairs[i:i + PAIR_GROUP] for i in range(0, len(pairs), PAIR_GROUP)]
    for g, grp in enumerate(groups):
        chk_bulk.append(f'''/-- Pair checks {grp[0]} to {grp[-1]}. -/
theorem pairs_{g} : [{", ".join(f"({p}, {q})" for (p, q) in grp)}].all
    (fun pq => pairOk dm pq.1 pq.2 R H (pairChoice dm R C pq.1 pq.2)) = true := by
  decide +kernel
''')
    chk_bulk.append(f'''/-- All {len(pairs)} pair checks, assembled without recomputation. -/
theorem hpairs : allPairs dm R H C = true := by
  rw [allPairs, show pairList dm = {" ++ ".join("[" + ", ".join(f"({p}, {q})" for (p, q) in grp) + "]" for grp in groups)} from by decide]
  simp only [List.all_append, Bool.and_true, Bool.true_and,
    {", ".join(f"pairs_{g}" for g in range(len(groups)))}]
''')

    # ---------------- the table, the entries, the contract ----------------
    chk_tab = [f'''theorem hT : T = packIdx ms dm L := by decide +kernel

theorem hlast : lastAll ms dm = true := by decide +kernel

theorem hchk : ms.consistentCheck = true := by decide +kernel

theorem hrps : {cfg}.rankPairs = buildRank goodMask wl := by decide +kernel

theorem hlwchk : {cfg}.rankPairs.all (fun q => q.2 &&& ms.full == q.2) = true := by
  decide +kernel
''']
    nch = (N + FREE_CHUNK - 1) // FREE_CHUNK
    for k in range(nch):
        chk_tab.append(f'''theorem hfree_{k} : freeCheckT ms dm P (knownMask dm R) goodMask ({k} * {FREE_CHUNK}) {FREE_CHUNK} = true := by
  decide +kernel
''')
    cases = SEP2.join(f"| {k}, _ => exact hfree_{k}" for k in range(nch))
    chk_tab.append(f'''theorem hfree : ∀ k, k < {nch} →
    freeCheckT ms dm P (knownMask dm R) goodMask (k * {FREE_CHUNK}) {FREE_CHUNK} = true := by
  intro k hk
  match k, hk with
  {cases}
  | k + {nch}, h => exact absurd h (by omega)
''')
    for c in chunk_names:
        chk_tab.append(f'''theorem h{c} : resCheckT ms {cfg}.certMask P {c} = true := by decide +kernel
''')
    chk_tab.append(f'''theorem hE : resCheckT ms {cfg}.certMask P E = true := by
  simp only [E, EL, List.flatten_cons, List.flatten_nil, List.append_nil,
    {", ".join(f"E_{r}" for r in range(nlev))}, resCheckT_append, resCheckT_nil,
    {", ".join(f"h{c}" for c in chunk_names)}, Bool.and_true]

theorem hU : {cfg}.certMask = levelUnion wl := by decide +kernel

theorem hzero : (zeroMask dm R' &&& ((2 ^ 3 ^ dm - 1) ^^^ knownMask dm R)) == 0 := by
  decide +kernel

theorem hnz : (nonZero dm R' &&&
    ((2 ^ 3 ^ dm - 1) ^^^ buildMask (resPieces E (pieceCount dm)))) == 0 := by
  decide +kernel

theorem hctr : contractCheckH cf dm R (buildMask (resPieces E (pieceCount dm))) = true := by
  decide +kernel
''')

    # ---------------- the levels and the witnesses ----------------
    chk_lev = []
    for r in range(nlev):
        chk_lev.append(f'''theorem hlev_{r} : levelCheck ms dm R' wl EL {r} = true := by decide +kernel
''')
    lcases = SEP2.join(f"| {r}, _ => exact hlev_{r}" for r in range(nlev))
    chk_lev.append(f'''theorem hlev : ∀ r, r < wl.length → levelCheck ms dm R' wl EL r = true := by
  intro r hr
  rw [show wl.length = {nlev} from rfl] at hr
  match r, hr with
  {lcases}
  | r + {nlev}, h => exact absurd h (by omega)
''')
    for r in range(nlev):
        chk_lev.append(f'''theorem hwit_{r} : witCheckL ms dm P wlL EL {r} = true := by decide +kernel
''')
    wcases = SEP2.join(f"| {r}, _ => exact hwit_{r}" for r in range(nlev))
    chk_lev.append(f'''theorem hwitB : ∀ r, r < wl.length → witCheckL ms dm P wlL EL r = true := by
  intro r hr
  rw [show wl.length = {nlev} from rfl] at hr
  match r, hr with
  {wcases}
  | r + {nlev}, h => exact absurd h (by omega)
''')

    # ---------------- the chord settling ----------------
    okgroups = [pairs[i:i + PAIR_GROUP] for i in range(0, len(pairs), PAIR_GROUP)]
    chk_ok = []
    for g, grp in enumerate(okgroups):
        chk_ok.append(f'''/-- Settling checks for chords {grp[0]} to {grp[-1]}. -/
theorem hok_{g} : [{", ".join(f"({q}, {p})" for (q, p) in grp)}].all
    (fun qp => okCheckT ms dm P {cfg}.certMask ({cfg}.okf qp.1 qp.2)
      (okBig dm qp.1 qp.2 R' H') (Sf qp.1 qp.2)) = true := by
  decide +kernel
''')

    # ---------------- the assembly ----------------
    final = [f'''theorem hok : allOkT ms dm P {cfg}.certMask {cfg}.okf Sf R' H' = true := by
  rw [allOkT, show pairList dm = {" ++ ".join("[" + ", ".join(f"({q}, {p})" for (q, p) in grp) + "]" for grp in okgroups)} from by decide]
  simp only [List.all_append, Bool.and_true, Bool.true_and,
    {", ".join(f"hok_{g}" for g in range(len(okgroups)))}]

/-- **Configuration {idx + 1} is C-reducible.** -/
theorem reducible : ReducibleInRange {idx} ({idx} + 1) theConfigs :=
  reducible_range_one
    (cfReducible_of_hybridT cf dm hcf R H C (by rw [hH, length_minPerm]) (by decide) hH hgood hchoice hpairs
      ms hlen hchk {cfg}.certMask goodMask wl {cfg}.rankPairs hrps hlwchk
      {cfg}.okf hwalk
      L (by decide) (by decide) (by decide) T hT {npieces} (by decide) P rfl hlast
      {FREE_CHUNK} {nch} (by decide) (by decide) hfree EL rfl E rfl hE hU R' H' hH' htop hlev
      wlL rfl hwitB hzero hnz Sf hok hctr)
''']

    base_imports = ['FourColor.Bulk.HybridT', 'FourColor.Bulk.Lit', f'FourColor.Mask.{cfg}',
                    'FourColor.Configurations']
    summary = (f'Ring size {n}.  The bulk certificate settles all but a residue of the contract\n'
               f'colourings; the residue is certified by the chord-aware mask walk of\n'
               f'`FourColor.Mask.{cfg}` over a universe of {N} traces, {len(entries)} of\n'
               f'them entries in {nlev} levels, whose free witnesses the bulk certificate knows.\n'
               f'Generated by `scripts/gen_hybt_jobs.py`.\n')
    os.makedirs(outdir, exist_ok=True)
    written = []

    def write_named(name, imports, doc, body):
        path = os.path.join(outdir, f'{name}.lean')
        open(path, 'w').write(module(hyb, imports, doc, body))
        written.append(path)

    if not split:
        write_named(hyb, base_imports, f'# Configuration {idx + 1} is C-reducible\n\n' + summary,
                    defs + chk_bulk + chk_tab + chk_lev + chk_ok + final)
    else:
        dmod = f'FourColor.Bulk.Cfg.{hyb}D'
        kparts = [chk_ok[i::OK_PARTS] for i in range(OK_PARTS)]
        write_named(f'{hyb}D', base_imports,
                    f'# Configuration {idx + 1}: the certificate data\n\n' + summary +
                    'This module holds the data; the checks are in the sibling modules.\n', defs)
        write_named(f'{hyb}A', [dmod], f'# Configuration {idx + 1}: the bulk pair checks\n\n', chk_bulk)
        write_named(f'{hyb}B', [dmod], f'# Configuration {idx + 1}: the table, the entries and the contract\n\n',
                    chk_tab)
        write_named(f'{hyb}C', [dmod], f'# Configuration {idx + 1}: the levels and the witnesses\n\n', chk_lev)
        for i, kp in enumerate(kparts):
            write_named(f'{hyb}K{i + 1}', [dmod], f'# Configuration {idx + 1}: chord settling, part {i + 1}\n\n', kp)
        write_named(hyb, [f'FourColor.Bulk.Cfg.{hyb}{s}' for s in ['A', 'B', 'C'] + [f'K{i + 1}' for i in range(OK_PARTS)]],
                    f'# Configuration {idx + 1} is C-reducible\n\n' + summary +
                    f'The checks are spread over the `{hyb}A`..`{hyb}K{OK_PARTS}` modules so that\n'
                    'they build in parallel; this module assembles them.\n', final)
    return written


if __name__ == '__main__':
    args = sys.argv[1:]
    force_split = None
    if '--split' in args:
        args.remove('--split'); force_split = True
    if '--single' in args:
        args.remove('--single'); force_split = False
    planesdir, gendir, certdir, outdir = args[:4]
    for i in [int(x) for x in args[4:]]:
        D = MC.build_all(i, planesdir, gendir, certdir)
        out = emit(i, D, outdir, force_split)
        print(f'cfg{i:03d}: universe {D["N"]} entries {len(D["entries"])} levels {D["maxr"] + 1} '
              f'planes {D["nplanes"]} -> {len(out)} module(s): {", ".join(os.path.basename(o) for o in out)}')

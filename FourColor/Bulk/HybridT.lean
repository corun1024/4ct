import FourColor.Bulk.HybridC
import FourColor.Bulk.Lanes

/-!
# The hybrid certificate, read through the packed index table

`FourColor.Bulk.HybridC` bridges the residual walk and the bulk certificate by
computing each universe trace's bulk index from the colour masks — a list walk
per trace that the kernel cannot afford at scale.  Here every per-trace fact
is read off the packed table `packIdx` of `FourColor.Bulk.Lanes` instead
(`laneP`: a shift and a mask on one piece of the table), and the one remaining
per-trace condition of the correspondence — that a trace's completing colour is
the sum of its first `m` — becomes two plane equations (`lastAll`).

## Main results

* `lastOk_of_lastAll` — the plane equations give every trace's completion.
* `cfReducible_of_hybridT` — **the theorem a generated residual module applies.**
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Pieces of the packed table -/

/-- Lanes per piece: `2^18` bits. -/
def lanesPerPiece : ℕ := 8192

/-- The table in pieces of `2^18` bits. -/
def lanePieces (T k : ℕ) : List ℕ :=
  (List.range k).map fun c => (T >>> (c * (32 * lanesPerPiece))) &&& (2 ^ (32 * lanesPerPiece) - 1)

/-- Lane `j`, read from the pieces. -/
def laneP (P : List ℕ) (j : ℕ) : ℕ :=
  ((P.getD (j / lanesPerPiece) 0) >>> (32 * (j % lanesPerPiece))) &&& (2 ^ 32 - 1)

theorem laneP_lanePieces (T k j : ℕ) (hj : j < k * lanesPerPiece) :
    laneP (lanePieces T k) j = lane T j := by
  unfold laneP lanePieces lane
  have hpos : 0 < lanesPerPiece := by decide
  have hc : j / lanesPerPiece < k := by rw [Nat.div_lt_iff_lt_mul hpos]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  simp only [Option.map_some, Option.getD_some]
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hq : q < 32
  · have hlt : 32 * (j % lanesPerPiece) + q < 32 * lanesPerPiece := by
      have := Nat.mod_lt j hpos
      unfold lanesPerPiece at *; omega
    have heq : j / lanesPerPiece * (32 * lanesPerPiece) + (32 * (j % lanesPerPiece) + q) = 32 * j + q := by
      have := Nat.div_add_mod j lanesPerPiece
      unfold lanesPerPiece at *; omega
    simp [hq, hlt, heq]
  · simp [hq]

/-! ### The completing colour, for every trace at once -/

/-- The high-bit plane at position `p`: colours `c2` and `c3`. -/
def hiPlane (ms : Masks) (p : ℕ) : ℕ := ms.colourMask p c2 ||| ms.colourMask p c3

/-- The low-bit plane at position `p`: colours `c1` and `c3`. -/
def loPlane (ms : Masks) (p : ℕ) : ℕ := ms.colourMask p c1 ||| ms.colourMask p c3

/-- The completing colour of every trace is the sum of its first `m`: the
`xor` of the first `m` planes agrees with plane `m`, in both bits. -/
def lastAll (ms : Masks) (m : ℕ) : Bool :=
  ((((List.range m).foldr (fun p acc => hiPlane ms p ^^^ acc) 0) ^^^ hiPlane ms m) &&& ms.full == 0) &&
  ((((List.range m).foldr (fun p acc => loPlane ms p ^^^ acc) 0) ^^^ loPlane ms m) &&& ms.full == 0)

theorem testBit_foldr_xor (f : ℕ → ℕ) (j : ℕ) :
    ∀ l : List ℕ, (l.foldr (fun p acc => f p ^^^ acc) 0).testBit j =
      l.foldr (fun p b => xor ((f p).testBit j) b) false
  | [] => by simp
  | p :: l => by simp only [List.foldr_cons, Nat.testBit_xor, testBit_foldr_xor f j l]

theorem hi_sum : ∀ l : List Color, l.sum.hi = l.foldr (fun c b => xor c.hi b) false
  | [] => rfl
  | c :: l => by rw [List.sum_cons, hi_add, List.foldr_cons, hi_sum l]

theorem lo_sum : ∀ l : List Color, l.sum.lo = l.foldr (fun c b => xor c.lo b) false
  | [] => rfl
  | c :: l => by rw [List.sum_cons, lo_add, List.foldr_cons, lo_sum l]

theorem Color.eq_of_hi_lo {c d : Color} (h1 : c.hi = d.hi) (h2 : c.lo = d.lo) : c = d := by
  cases c <;> cases d <;> simp_all [hi, lo]

theorem hi_colourAt (ms : Masks) (hc : ms.Consistent) {p j : ℕ} (hp : p < ms.len)
    (hj : j < ms.width) : (ms.colourAt p j).hi = (hiPlane ms p).testBit j := by
  unfold hiPlane
  rw [Nat.testBit_or]
  have h2 := ms.colourAt_eq_iff hp hj hc (c := c2) (by simp)
  have h3 := ms.colourAt_eq_iff hp hj hc (c := c3) (by simp)
  have h1 := ms.colourAt_eq_iff hp hj hc (c := c1) (by simp)
  have h0 := ms.colourAt_ne_c0 hp hj hc
  cases hcol : ms.colourAt p j
  · exact absurd hcol h0
  · rw [hcol] at h1 h2 h3
    simp only [true_iff, reduceCtorEq, false_iff] at h1 h2 h3
    simp [hi, h2, h3]
  · rw [hcol] at h2
    simp only [true_iff] at h2
    simp [hi, h2]
  · rw [hcol] at h3
    simp only [true_iff] at h3
    simp [hi, h3]

theorem lo_colourAt (ms : Masks) (hc : ms.Consistent) {p j : ℕ} (hp : p < ms.len)
    (hj : j < ms.width) : (ms.colourAt p j).lo = (loPlane ms p).testBit j := by
  unfold loPlane
  rw [Nat.testBit_or]
  have h2 := ms.colourAt_eq_iff hp hj hc (c := c2) (by simp)
  have h3 := ms.colourAt_eq_iff hp hj hc (c := c3) (by simp)
  have h1 := ms.colourAt_eq_iff hp hj hc (c := c1) (by simp)
  have h0 := ms.colourAt_ne_c0 hp hj hc
  cases hcol : ms.colourAt p j
  · exact absurd hcol h0
  · rw [hcol] at h1
    simp only [true_iff] at h1
    simp [lo, h1]
  · rw [hcol] at h1 h2 h3
    simp only [true_iff, reduceCtorEq, false_iff] at h1 h2 h3
    simp [lo, h1, h3]
  · rw [hcol] at h3
    simp only [true_iff] at h3
    simp [lo, h3]

/-- The trace's first `m` colours, as the walk sees them. -/
theorem take_traceOf (ms : Masks) (m : ℕ) (hm : m ≤ ms.len) (j : ℕ) :
    (ms.traceOf j).take m = (List.range m).map fun p => ms.colourAt p j := by
  unfold Masks.traceOf
  rw [← List.map_take, List.take_range, Nat.min_eq_left hm]

/-- **The plane equations give every trace's completion.** -/
theorem lastOk_of_lastAll (ms : Masks) (hc : ms.Consistent) {m : ℕ} (hlen : ms.len = m + 1)
    (h : lastAll ms m = true) {j : ℕ} (hj : j < ms.width) : lastOk ms m j = true := by
  unfold lastAll at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hhi, hlo⟩ := h
  unfold lastOk
  rw [partialOf_bigOf ms m j (by omega), trCodes_eq ms hc hj, take_traceOf ms m (by omega)]
  have hget : (ms.traceOf j).getD m 0 = ms.colourAt m j := by
    unfold Masks.traceOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [hget, decide_eq_true_eq]
  have hfull := ms.testBit_full hj
  have key : ∀ (plane : Masks → ℕ → ℕ) (proj : Color → Bool),
      (∀ p, p < ms.len → proj (ms.colourAt p j) = (plane ms p).testBit j) →
      ((List.range m).foldr (fun p acc => plane ms p ^^^ acc) 0 ^^^ plane ms m) &&& ms.full = 0 →
      (∀ l : List Color, proj l.sum = l.foldr (fun c b => xor (proj c) b) false) →
      proj (ms.colourAt m j) = proj (((List.range m).map fun p => ms.colourAt p j).sum) := by
    intro plane proj hproj hz hsum
    have hb := congrArg (fun x => x.testBit j) hz
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hfull, Bool.and_true] at hb
    rw [testBit_foldr_xor] at hb
    rw [hsum, hproj m (by omega)]
    have hfold : ∀ l : List ℕ, (∀ p ∈ l, p < ms.len) →
        (l.map fun p => ms.colourAt p j).foldr (fun c b => xor (proj c) b) false =
          l.foldr (fun p b => xor ((plane ms p).testBit j) b) false := by
      intro l hl
      induction l with
      | nil => rfl
      | cons p l ih =>
        simp only [List.map_cons, List.foldr_cons]
        rw [hproj p (hl p List.mem_cons_self), ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    rw [hfold _ (fun p hp => by have := List.mem_range.mp hp; omega)]
    revert hb
    generalize (List.range m).foldr (fun p b => xor ((plane ms p).testBit j) b) false = A
    generalize (plane ms m).testBit j = B
    cases A <;> cases B <;> simp
  apply Color.eq_of_hi_lo
  · exact key hiPlane Color.hi (fun p hp => hi_colourAt ms hc hp hj) hhi hi_sum
  · exact key loPlane Color.lo (fun p hp => lo_colourAt ms hc hp hj) hlo lo_sum

/-- The full mask, as a generated module spells it: no arithmetic on the width. -/
theorem full_eq_shiftLeft (ms : Masks) : ms.full = Nat.shiftLeft 1 ms.width - 1 := by
  show 2 ^ ms.width - 1 = 1 <<< ms.width - 1
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-! ### The checks -/

/-- The residual entries: each carries its bulk index, as the table says. -/
def resCheckT (ms : Masks) (certMask : ℕ) (P : List ℕ) (E : List (ℕ × ℕ)) : Bool :=
  E.all fun e => decide (e.1 < ms.width) && certMask.testBit e.1 && (laneP P e.1 == e.2)

/-- Every free witness is known in the bulk sense. -/
def freeCheckT (ms : Masks) (m : ℕ) (P : List ℕ) (known goodMask : ℕ) (lo n : ℕ) : Bool :=
  let PK := pieces known (pieceCount m)
  (List.range' lo n).all fun j => !goodMask.testBit j || memPiece PK (laneP P j)

/-- A witness level's masks name traces whose permutation is an entry of the level. -/
def witCheckT (ms : Masks) (m : ℕ) (P : List ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (EL : List (List (ℕ × ℕ))) (r : ℕ) : Bool :=
  let PL := pieces (buildMask (resPieces (EL.getD r []) (pieceCount m))) (pieceCount m)
  (wl.getD r (0, [])).2.all fun gm =>
    (List.range ms.width).all fun j =>
      !gm.2.testBit j || memPiece PL (permIdx gm.1 m (laneP P j))

/-- The small-universe mask of a list of indices. -/
def smallMaskIdx (ms : Masks) (S : List ℕ) : ℕ :=
  buildMask (resPieces (S.map fun j => (0, j)) (smallPieceCount ms))

theorem mem_of_testBit_smallMaskIdx (ms : Masks) {S : List ℕ} {j : ℕ} (hj : j < ms.width)
    (h : (smallMaskIdx ms S).testBit j = true) : j ∈ S := by
  unfold smallMaskIdx at h
  obtain ⟨e', he', hei⟩ := mem_of_testBit_buildMask_resPieces (lt_smallPieceCount_mul ms hj) h
  rw [List.mem_map] at he'
  obtain ⟨j', hj', rfl⟩ := he'
  simp only at hei
  rw [← hei]; exact hj'

/-- The witness levels with the witnesses listed by index; `wlOf` turns them into
the masks `buildRank` consumes. -/
def wlOf (ms : Masks) (wlL : List (ℕ × List (EdgePerm × List ℕ))) :
    List (ℕ × List (EdgePerm × ℕ)) :=
  wlL.map fun ent => (ent.1, ent.2.map fun gjs => (gjs.1, smallMaskIdx ms gjs.2))

theorem getD_wlOf (ms : Masks) (wlL : List (ℕ × List (EdgePerm × List ℕ))) {r : ℕ}
    (hr : r < wlL.length) :
    (wlOf ms wlL).getD r (0, []) =
      ((wlL.getD r (0, [])).1, (wlL.getD r (0, [])).2.map fun gjs => (gjs.1, smallMaskIdx ms gjs.2)) := by
  unfold wlOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hr]
  rfl

/-- A witness level's lists name traces whose permutation is an entry of the level. -/
def witCheckL (ms : Masks) (m : ℕ) (P : List ℕ) (wlL : List (ℕ × List (EdgePerm × List ℕ)))
    (EL : List (List (ℕ × ℕ))) (r : ℕ) : Bool :=
  let PL := pieces (buildMask (resPieces (EL.getD r []) (pieceCount m))) (pieceCount m)
  (wlL.getD r (0, [])).2.all fun gjs =>
    gjs.2.all fun j => decide (j < ms.width) && memPiece PL (permIdx gjs.1 m (laneP P j))

/-- A chord's settling mask is its list of settled entries, each settled in the bulk. -/
def okCheckT (ms : Masks) (m : ℕ) (P : List ℕ) (certMask okS okB : ℕ) (S : List ℕ) : Bool :=
  let PB := pieces okB (pieceCount m)
  (okS == smallMaskIdx ms S) &&
    S.all fun j => decide (j < ms.width) && certMask.testBit j && memPiece PB (laneP P j)

/-- Every chord's settling check, as one boolean. -/
def allOkT (ms : Masks) (m : ℕ) (P : List ℕ) (certMask : ℕ) (ok : ℕ → ℕ → ℕ)
    (S : ℕ → ℕ → List ℕ) (R' H' : List ℕ) : Bool :=
  (pairList m).all fun qp =>
    okCheckT ms m P certMask (ok qp.1 qp.2) (okBig m qp.1 qp.2 R' H') (S qp.1 qp.2)

/-- Indices packed eighteen bits each, unpacked from a numeral. -/
def unpackIdx (N : ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => ((N >>> (18 * t)) &&& (2 ^ 18 - 1)) :: unpackIdx N t

theorem resCheckT_append (ms : Masks) (certMask : ℕ) (P : List ℕ) (E₁ E₂ : List (ℕ × ℕ)) :
    resCheckT ms certMask P (E₁ ++ E₂) =
      (resCheckT ms certMask P E₁ && resCheckT ms certMask P E₂) := by
  unfold resCheckT; rw [List.all_append]

theorem resCheckT_nil (ms : Masks) (certMask : ℕ) (P : List ℕ) : resCheckT ms certMask P [] = true := rfl

/-! ### The theorem -/

/-- **C-reducibility from the bulk certificate and a chord-aware residual walk,
read through the packed index table.** -/
theorem cfReducible_of_hybridT (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
    (R H C : List ℕ) (hlenH : R.length = H.length) (hClen : m < 2 ^ C.length)
    (hH : H = minPerm m R) (hgood : goodCheck m R cf.prog = true)
    (hchoice : choiceCheck m R C = true) (hpairs : allPairs m R H C = true)
    -- the residual walk
    (ms : Masks) (hlen : ms.len = m + 1) (hchk : ms.consistentCheck = true)
    (certMask goodMask : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (rps : RankPairs) (hrps : rps = Masks.buildRank goodMask wl)
    (hlwchk : rps.all (fun q => q.2 &&& ms.full == q.2) = true)
    (ok : ℕ → ℕ → ℕ)
    (hwalk : ms.walkC ok rps (List.range ms.len) [] ms.full certMask = true)
    -- the packed table
    (L : ℕ) (hL : L < 40) (hw : ms.width ≤ 2 ^ L) (hm : 2 * 3 ^ m < 2 ^ 32)
    (T : ℕ) (hT : T = packIdx ms m L) (k : ℕ) (hk : ms.width ≤ k * lanesPerPiece)
    (P : List ℕ) (hP : P = lanePieces T k) (hlast : lastAll ms m = true)
    -- the free witnesses
    (chunk nch : ℕ) (hchunk : 0 < chunk) (hcov : ms.width ≤ nch * chunk)
    (hfree : ∀ i, i < nch → freeCheckT ms m P (knownMask m R) goodMask (i * chunk) chunk = true)
    -- the entries, by level
    (EL : List (List (ℕ × ℕ))) (hEL : EL.length = wl.length)
    (E : List (ℕ × ℕ)) (hEdef : E = EL.flatten)
    (hE : resCheckT ms certMask P E = true)
    (hU : certMask = levelUnion wl)
    -- the residual rank planes
    (R' H' : List ℕ) (hH' : H' = minPerm m R') (htop : wl.length + 1 < rankTop R')
    (hlev : ∀ r, r < wl.length → levelCheck ms m R' wl EL r = true)
    (wlL : List (ℕ × List (EdgePerm × List ℕ))) (hwl : wl = wlOf ms wlL)
    (hwitB : ∀ r, r < wl.length → witCheckL ms m P wlL EL r = true)
    (hzero : (zeroMask m R' &&& ((2 ^ 3 ^ m - 1) ^^^ knownMask m R)) == 0)
    (hnz : (nonZero m R' &&&
      ((2 ^ 3 ^ m - 1) ^^^ buildMask (resPieces E (pieceCount m)))) == 0)
    (S : ℕ → ℕ → List ℕ) (hok : allOkT ms m P certMask ok S R' H' = true)
    (hctr : contractCheckH cf m R (buildMask (resPieces E (pieceCount m))) = true) :
    CfReducible cf := by
  set P₀ := (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) with hP₀
  have hknown := known_coclosure cf m hcf R H C hlenH hClen hH hgood hchoice hpairs
  have hc : ms.Consistent := ms.consistent_of_check hchk
  subst hEdef
  set E := EL.flatten with hEdef
  -- the table
  have hlane : ∀ j, j < ms.width → laneP P j = bigOf ms m j := by
    intro j hj
    rw [hP, laneP_lanePieces _ _ _ (lt_of_lt_of_le hj hk), hT,
      lane_packIdx ms hc hL hm (by omega) hw hj]
  have hlastOk : ∀ j, j < ms.width → lastOk ms m j = true :=
    fun j hj => lastOk_of_lastAll ms hc hlen hlast hj
  have htrace : ∀ j, j < ms.width → traceOf m (bigOf ms m j) = ms.traceOf j :=
    fun j hj => traceOf_bigOf ms hc hlen hj (hlastOk j hj)
  -- free witnesses are in the co-closure
  have hgoodP : ∀ j, j < ms.width → goodMask.testBit j = true → KempeCoclosure P₀ (ms.traceOf j) := by
    intro j hj hgj
    have hi : j / chunk < nch := by
      rw [Nat.div_lt_iff_lt_mul hchunk]; omega
    have h := hfree (j / chunk) hi
    unfold freeCheckT at h
    rw [List.all_eq_true] at h
    have hmem : j ∈ List.range' (j / chunk * chunk) chunk := by
      rw [List.mem_range'_1]
      have := Nat.div_add_mod j chunk
      have := Nat.mod_lt j hchunk
      constructor <;> nlinarith [Nat.div_mul_le_self j chunk]
    have := h j hmem
    simp only [hgj, Bool.not_true, Bool.false_or, hlane j hj] at this
    rw [memPiece_pieces _ _ _ (lt_pieceCount_mul (bigOf_lt ms m j))] at this
    rw [← htrace j hj]
    exact hknown _ (bigOf_lt ms m j) this
  -- what the entry list says of an entry
  have hentry : ∀ e ∈ E, e.1 < ms.width ∧ certMask.testBit e.1 = true ∧
      bigOf ms m e.1 = e.2 ∧ traceOf m e.2 = ms.traceOf e.1 := by
    intro e he
    unfold resCheckT at hE
    rw [List.all_eq_true] at hE
    have := hE e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨hew, hecert⟩, hebig⟩ := this
    rw [hlane e.1 hew] at hebig
    exact ⟨hew, hecert, hebig, by rw [← hebig]; exact htrace e.1 hew⟩
  -- a certified index has a level, and is an entry of it
  have hlevel : ∀ i, i < ms.width → certMask.testBit i = true →
      ∃ r, r < wl.length ∧ (wl.getD r (0, [])).1.testBit i = true := by
    intro i hi hci
    rw [hU, testBit_levelUnion] at hci
    obtain ⟨ent, hent, hb⟩ := hci
    obtain ⟨r, hr, hget⟩ := exists_getD_of_mem (0, []) wl ent hent
    exact ⟨r, hr, by rw [hget]; exact hb⟩
  have hlevelE : ∀ r, r < wl.length → ∀ i, (wl.getD r (0, [])).1.testBit i = true →
      i < ms.width → ∃ e ∈ EL.getD r [], e.1 = i := by
    intro r hr i hb hi
    have hl := hlev r hr
    unfold levelCheck at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    rw [hl.1] at hb
    unfold smallMask at hb
    obtain ⟨e', he', hei⟩ :=
      mem_of_testBit_buildMask_resPieces (lt_smallPieceCount_mul ms hi) hb
    rw [List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact ⟨e, he, hei⟩
  have hsub : ∀ r, r < wl.length → ∀ e ∈ EL.getD r [], e ∈ E := by
    intro r hr e he
    rw [hEdef, List.mem_flatten]
    exact ⟨EL.getD r [], getD_mem [] EL r (by omega), he⟩
  -- the rank of an entry of level `r` is `r + 1`
  have hval : ∀ r, r < wl.length → ∀ e ∈ EL.getD r [], val R' e.2 = r + 1 := by
    intro r hr e he
    have hl := hlev r hr
    unfold levelCheck at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    have hbig : e.2 < 3 ^ m := by
      rw [← (hentry e (hsub r hr e he)).2.2.1]; exact bigOf_lt ms m e.1
    have hbit := testBit_buildMask_resPieces_of_mem he (lt_pieceCount_mul hbig)
    have h0 := congrArg (fun x => x.testBit e.2) hl.2
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
      hbit, hbig, decide_true, Bool.true_and, Bool.true_xor, testBit_valMask m R' _ _ hbig] at h0
    simpa using h0
  -- the rank function
  set rank : List Color → ℕ := rankOf m R' with hrank
  have hrankE : ∀ e ∈ E, rank (ms.traceOf e.1) = val R' e.2 := by
    intro e he
    obtain ⟨-, -, hbig, htr⟩ := hentry e he
    rw [hrank, ← htr, rankOf_traceOf m R' (by rw [← hbig]; exact bigOf_lt ms m e.1)]
  have hgoodAllPerm : ∀ (g : EdgePerm) (j : ℕ), j < 3 ^ m →
      (knownMask m R).testBit (permIdx g m j) = (knownMask m R).testBit j :=
    fun g j hj => permClose_permIdx m _ g j hj
  have hzero' : zeroMask m R' &&& ((2 ^ 3 ^ m - 1) ^^^ knownMask m R) = 0 := by
    simpa using hzero
  -- the hypotheses of the chord-aware walk
  have hlw := ms.hlw_of_check rps hlwchk
  have hwit := ms.hwit_of_buildRank certMask goodMask (P := KempeCoclosure P₀) wl hgoodP
    (fun ent hent gm hgm i hi hb => by
      obtain ⟨r, hr, hget⟩ := exists_getD_of_mem (0, []) wl ent hent
      have hl := hlev r hr
      unfold levelCheck at hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      rw [← hget]
      -- the witness check of level `r`
      have hrL : r < wlL.length := by rw [hwl, wlOf, List.length_map] at hr; exact hr
      have hgetL : (wl.getD r (0, [])).2 =
          (wlL.getD r (0, [])).2.map fun gjs => (gjs.1, smallMaskIdx ms gjs.2) := by
        rw [hwl, getD_wlOf ms wlL hrL]
      have hgm' : gm ∈ (wlL.getD r (0, [])).2.map fun gjs => (gjs.1, smallMaskIdx ms gjs.2) := by
        rw [← hgetL, hget]; exact hgm
      rw [List.mem_map] at hgm'
      obtain ⟨gjs, hgjs, rfl⟩ := hgm'
      simp only at hb
      have hiS : i ∈ gjs.2 := mem_of_testBit_smallMaskIdx ms hi hb
      have h := hwitB r hr
      unfold witCheckL at h
      rw [List.all_eq_true] at h
      have h := h gjs hgjs
      rw [List.all_eq_true] at h
      have h := h i hiS
      simp only [Bool.and_eq_true, decide_eq_true_eq, hlane i hi] at h
      obtain ⟨-, h⟩ := h
      have hpl : permIdx gjs.1 m (bigOf ms m i) < 3 ^ m := permIdx_lt _ (bigOf_lt ms m i)
      rw [memPiece_pieces _ _ _ (lt_pieceCount_mul hpl)] at h
      obtain ⟨e, he, hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hpl) h
      obtain ⟨hew, hecert, -, htr⟩ := hentry e (hsub r hr e he)
      refine ⟨e.1, hew, hecert, ?_, ?_⟩
      · rw [hl.1]
        unfold smallMask
        have hmem' : e.swap ∈ (EL.getD r []).map Prod.swap := List.mem_map_of_mem he
        exact testBit_buildMask_resPieces_of_mem hmem' (by
          show e.1 < smallPieceCount ms * pieceBits
          exact lt_smallPieceCount_mul ms hew)
      · rw [← htr, hej, traceOf_permIdx, htrace i hi])
  rw [← hrps] at hwit
  have hlvl : ∀ (pre : RankPairs) (q : ℕ × ℕ) (post : RankPairs), rps = pre ++ q :: post →
      ∀ i, i < ms.width → certMask.testBit i = true → q.1.testBit i = true →
        rank (ms.traceOf i) = pre.length + 1 := by
    intro pre q post hsplit i hi hci hb
    have hr : pre.length < wl.length := by
      have := congrArg List.length hsplit
      rw [hrps, length_buildRank] at this
      simp at this; omega
    have hq : q.1 = (wl.getD pre.length (0, [])).1 := by
      rw [← getD_buildRank_fst goodMask wl pre.length, ← hrps, hsplit,
        Masks.getD_append_length]
    rw [hq] at hb
    obtain ⟨e, he, rfl⟩ := hlevelE pre.length hr i hb hi
    rw [hrankE e (hsub _ hr e he), hval _ hr e he]
  have hcovL : ∀ i, i < ms.width → certMask.testBit i = true → ∃ q ∈ rps, q.1.testBit i = true := by
    intro i hi hci
    obtain ⟨r, hr, hb⟩ := hlevel i hi hci
    refine ⟨rps.getD r (0, 0), getD_mem _ _ _ (by rw [hrps, length_buildRank]; exact hr), ?_⟩
    rw [hrps, getD_buildRank_fst]; exact hb
  have hokW : ∀ q p i, i < ms.width → certMask.testBit i = true → (ok q p).testBit i = true →
      ∀ (w : Chromogram) (cs : List (ℕ × ℕ)), matchg [] (ms.traceOf i) w = true →
        chords w = some cs → (q, p) ∈ cs →
        ∃ et', matchg [] et' w = true ∧
          (KempeCoclosure P₀ et' ∨ ∃ g : EdgePerm, ms.Cert certMask (et'.map g) ∧
            rank (et'.map g) < rank (ms.traceOf i)) := by
    intro q p i hi hci hokb w cs hmw hcs hqp
    have hbiglt : bigOf ms m i < 3 ^ m := bigOf_lt ms m i
    have htr := htrace i hi
    -- the chord is a pair
    have hchord := chord_facts (by rw [← htr] at hmw; exact hmw) hcs hqp
    have hqlt : q < p := hchord.1
    have hpm : p ≤ m := by have := hchord.2.1; rw [length_traceOf] at this; omega
    -- the settling mask maps into the bulk one
    have hokB : (okBig m q p R' H').testBit (bigOf ms m i) = true := by
      unfold allOkT at hok
      rw [List.all_eq_true] at hok
      have h := hok (q, p) (mem_pairList.mpr ⟨hqlt, hpm⟩)
      unfold okCheckT at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hS, hall⟩ := h
      rw [hS] at hokb
      have hj := mem_of_testBit_smallMaskIdx ms hi hokb
      rw [List.all_eq_true] at hall
      have h := hall i hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, hlane i hi] at h
      rw [memPiece_pieces _ _ _ (lt_pieceCount_mul hbiglt)] at h
      exact h.2
    -- the trace ranks at its level
    obtain ⟨r, hr, hb⟩ := hlevel i hi hci
    obtain ⟨e, he, rfl⟩ := hlevelE r hr i hb hi
    have heE := hsub r hr e he
    obtain ⟨-, -, hbig, -⟩ := hentry e heE
    have hvtop : val R' (bigOf ms m e.1) < rankTop R' := by rw [hbig, hval r hr e he]; omega
    -- the witness, in the bulk space
    obtain ⟨et', hmet', hw'⟩ := witness_of_chord hH' (by rw [hH', length_minPerm]) hzero'
      hgoodAllPerm hbiglt hvtop (by rw [← htr] at hmw; exact hmw) hcs hqp hokB
    refine ⟨et', hmet', ?_⟩
    rcases hw' with ⟨j, hj, hkj, rfl⟩ | ⟨g, ⟨j, hj, hpos, hjtop, hje⟩, hlt⟩
    · exact Or.inl (hknown j hj hkj)
    · refine Or.inr ⟨g, ?_, ?_⟩
      · have hnzj : (nonZero m R').testBit j = true := by
          rw [testBit_nonZero R' hj]; simp [hpos, hjtop]
        have hnz' : nonZero m R' &&&
            ((2 ^ 3 ^ m - 1) ^^^ buildMask (resPieces E (pieceCount m))) = 0 := by
          simpa using hnz
        have h0 := congrArg (fun x => x.testBit j) hnz'
        simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
          Nat.zero_testBit, hnzj, hj, decide_true, Bool.true_and, Bool.true_xor] at h0
        have hbj : (buildMask (resPieces E (pieceCount m))).testBit j = true := by
          cases h : (buildMask (resPieces E (pieceCount m))).testBit j
          · rw [h] at h0; exact absurd h0 (by simp)
          · rfl
        obtain ⟨e', he', hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hj) hbj
        obtain ⟨hew', hecert', -, htr'⟩ := hentry e' he'
        refine ⟨e'.1, hew', hecert', ?_⟩
        rw [← htr', hej, hje]
      · rw [htr] at hlt
        exact hlt
  -- the residual walk certifies its traces, with the co-closure as the base predicate
  have hco := ms.coclosure_of_walkC hc certMask ok rps rank hlw hlvl hcovL hwit hokW hwalk
    (fun _ hi => ms.testBit_full hi)
  have hres : ∀ et, ms.Cert certMask et → KempeCoclosure P₀ et := fun et h =>
    kempeCoclosure_trans (fun _ h' => h') (hco et h)
  -- the contract
  unfold contractCheckH at hctr
  cases hcpc : cfctr cf.prog (List.replicate (cprsize cf.prog) false) (cfcontractMask cf) with
  | none => rw [hcpc] at hctr; exact absurd hctr (by simp)
  | some cpc =>
    rw [hcpc] at hctr
    simp only [Bool.and_eq_true, beq_iff_eq] at hctr
    obtain ⟨hvalid, hcov⟩ := hctr
    have hcc := contractCtree_of_check hcpc hvalid
    obtain ⟨cpc', hcpc', hsize, -⟩ := exists_cfctr_of_contractCtree hcc
    rw [hcpc] at hcpc'
    obtain rfl := Option.some.inj hcpc'
    have hsize' : cprsize cpc = m + 1 := by rw [hsize, hcf]
    refine cfReducible_of_coclosure hcc ?_
    intro es hes
    obtain ⟨j, hjlt, hbit, g, hg⟩ := contract_mem_bulk hsize' hes
    have hkn : (knownMask m R ||| permClose m (buildMask (resPieces E (pieceCount m)))).testBit j
        = true := by
      have := congrArg (fun x => x.testBit j) hcov
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
        hbit, hjlt, decide_true, Bool.true_and, Bool.true_xor] at this
      cases h : (knownMask m R ||| permClose m (buildMask (resPieces E (pieceCount m)))).testBit j
      · rw [h] at this; exact absurd this (by simp)
      · rfl
    rw [Nat.testBit_or, Bool.or_eq_true] at hkn
    rw [hg]
    apply kempeCoclosure_map g
    rcases hkn with hkn | hkn
    · exact hknown j hjlt hkn
    · obtain ⟨g', hg'⟩ := (testBit_permClose m _ j hjlt).mp hkn
      have hgj := permIdx_lt g' hjlt
      obtain ⟨e, heE, hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hgj) hg'
      obtain ⟨hew, hecert, -, htr⟩ := hentry e heE
      have hco' : KempeCoclosure P₀ (traceOf m (permIdx g' m j)) := by
        rw [← hej, htr]
        exact hres _ ⟨e.1, hew, hecert, rfl⟩
      rw [traceOf_permIdx] at hco'
      exact kempeCoclosure_of_map g' hco'

end Bulk
end FourColor

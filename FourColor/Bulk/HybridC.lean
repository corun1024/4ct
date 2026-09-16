import FourColor.Bulk.Hybrid
import FourColor.MaskChord

/-!
# C-reducibility from a bulk certificate and a chord-aware residual walk

The residual walk of `FourColor.MaskChord` drops a certified trace as soon as
a closed chord settles it.  What settles a trace is decided in the bulk index
space, where the flips along a chord are the block moves of `FourColor.Bulk.Pair`:
the residual entries get rank planes `R'` over the bulk universe (rank zero on
the traces the bulk certificate knows, `r + 1` on the entries of level `r`,
the top rank elsewhere), and a trace is settled by chord `(q, p)` when one of
its three flips ranks below it — `okBig`, one `pairW` per pair.  The walk's
settling masks live in the small universe; `okCheck` maps each into the bulk
one through the entry list.

## Main results

* `witness_of_chord` — a settled trace has a witness for any chromogram with
  that chord.
* `cfReducible_of_hybridC` — **the theorem a generated residual module applies.**
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Rank planes -/

/-- The traces of rank exactly `v`. -/
def valMask (m : ℕ) : List ℕ → ℕ → ℕ
  | [], v => if v = 0 then 2 ^ 3 ^ m - 1 else 0
  | a :: as, v => (if v % 2 = 1 then a else (2 ^ 3 ^ m - 1) ^^^ a) &&& valMask m as (v / 2)

theorem testBit_valMask (m : ℕ) : ∀ (R : List ℕ) (v i : ℕ), i < 3 ^ m →
    (valMask m R v).testBit i = decide (val R i = v) := by
  intro R
  induction R with
  | nil =>
    intro v i hi
    simp only [valMask, val]
    split
    · next h => subst h; simp [Nat.testBit_two_pow_sub_one, hi]
    · next h => simp [Nat.zero_testBit, Ne.symm h]
  | cons a as ih =>
    intro v i hi
    simp only [valMask, val, Nat.testBit_and, ih (v / 2) i hi]
    split
    · next h =>
      rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;> simp [ha] <;> omega
    · next h =>
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
      rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;> simp [ha, hi] <;> omega

/-! ### What a chord settles -/

/-- The traces chord `(q, p)` settles: compatible with the chord, and with one
of the three flips along it ranking below them. -/
def okBig (m q p : ℕ) (R H : List ℕ) : ℕ := compat m q p &&& pairW m q p R H

theorem pairOk_okBig {m q p : ℕ} (hqp : q < p) (hp : p ≤ m) (R H : List ℕ) :
    pairOk m q p R H (okBig m q p R H) = true := by
  unfold pairOk okBig
  simp only [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
    testBit_compat hqp hp]
  by_cases hi : i < 3 ^ m
  · simp only [hi, true_and, decide_true, Bool.true_xor]
    cases (pairW m q p R H).testBit i <;> simp
  · simp [hi]

/-- **A settled trace has a witness for every chromogram with that chord.**
The bulk-side counterpart of `hcert_of_bulk`'s case analysis, for a chord
`(a, b)` of the chromogram rather than a chosen position. -/
theorem witness_of_chord {m : ℕ} {R H : List ℕ} {goodAll : ℕ} (hH : H = minPerm m R)
    (hlenH : R.length = H.length)
    (hgood : zeroMask m R &&& ((2 ^ 3 ^ m - 1) ^^^ goodAll) = 0)
    (hgoodPerm : ∀ (g : EdgePerm) (j : ℕ), j < 3 ^ m →
      goodAll.testBit (permIdx g m j) = goodAll.testBit j)
    {i : ℕ} (hi : i < 3 ^ m) (htop : val R i < rankTop R) {w : Chromogram}
    (hm : matchg [] (traceOf m i) w = true) {cs : List (ℕ × ℕ)} (hcs : chords w = some cs)
    {a b : ℕ} (hab : (a, b) ∈ cs) (hok : (okBig m a b R H).testBit i = true) :
    ∃ et', matchg [] et' w = true ∧
      (PGood m goodAll et' ∨
        ∃ g : EdgePerm, SCert m R (et'.map g) ∧ rankOf m R (et'.map g) < rankOf m R (traceOf m i)) := by
  have h0 : (0 : Color) ∉ traceOf m i := matchg_notMem_zero _ _ _ hm
  have hbal : balanced 0 false w = true := by
    have h := (matchg_balanced hm).2
    simpa [traceOf] using h
  obtain ⟨hab12, hbl, hac, hbc, heven, hf1, hf2, hf3⟩ := chord_facts hm hcs hab
  rw [length_traceOf] at hbl
  have hbm : b ≤ m := by omega
  have ham : a < m := by omega
  have hcmp : (compat m a b).testBit i = true := by
    unfold okBig at hok
    rw [Nat.testBit_and, Bool.and_eq_true] at hok
    exact hok.1
  have hHinv : ∀ j, j < 3 ^ m → val H (togIdxs m (List.range' 0 (m + 1)) j) = val H j := by
    intro j hj; rw [hH]; exact val_minPerm_togAll R j hj
  have hspec := pairOk_spec hab12 hbm hlenH hHinv (pairOk_okBig hab12 hbm R H) i hi hok hcmp
  have hdig : ∀ k, k < m → ((traceOf m i).getD k 0 ≠ c1 ↔ digit k i ≠ 0) :=
    fun k hk => ⟨digit_ne_zero_of_getD hk, getD_ne_c1_of_digit hk⟩
  have hda : digit a i ≠ 0 := digit_ne_zero_of_getD ham hac
  have hdb : b < m → digit b i ≠ 0 := fun h => digit_ne_zero_of_getD h hbc
  rcases hspec with hlt | hlt | hlt
  · -- the chord alone
    let M := maskOf (fun r => decide (r = a ∨ r = b)) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔ (r = a ∨ r = b) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        rcases h with h | h <;> rw [h] <;> omega
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal [a, b] (by simp; omega) M ?_
      (matchg_flip M w _ 0 [] [] hm (hf1 M hMbit)) hlt
    intro k hk
    rw [hMbit]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact ⟨Or.inl h, by rw [h]; exact hda⟩
      · exact ⟨Or.inr h, by rw [h]; exact hdb (by omega)⟩
    · rintro ⟨h, -⟩; exact h
  · -- everything strictly inside
    let M := maskOf (fun r => decide (a < r ∧ r < b ∧ (traceOf m i).getD r 0 ≠ c1)) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔ (a < r ∧ r < b ∧ (traceOf m i).getD r 0 ≠ c1) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by omega, h⟩
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal (inside a b)
      (List.nodup_range' 1 Nat.one_pos) M ?_ (matchg_flip M w _ 0 [] [] hm (hf2 M hMbit)) hlt
    intro k hk
    rw [hMbit, inside, List.mem_range'_1, ← hdig k hk]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
  · -- the chord together with everything inside
    let M := maskOf (fun r => decide (r = a ∨ r = b ∨
      (a < r ∧ r < b ∧ (traceOf m i).getD r 0 ≠ c1))) (m + 1)
    have hMbit : ∀ r, M.testBit r = true ↔
        (r = a ∨ r = b ∨ (a < r ∧ r < b ∧ (traceOf m i).getD r 0 ≠ c1)) := by
      intro r
      rw [testBit_maskOf, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        rcases h with h | h | ⟨-, h2, -⟩ <;> first | (rw [h]; omega) | omega
    have hnodup : (a :: b :: inside a b).Nodup := by
      rw [List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, List.nodup_range' 1 Nat.one_pos⟩
      · simp [inside, List.mem_range'_1]; omega
      · simp [inside, List.mem_range'_1]; omega
    refine finish_of_lt hH hgood hgoodPerm hi htop hbal (a :: b :: inside a b) hnodup M ?_
      (matchg_flip M w _ 0 [] [] hm (hf3 M hMbit)) hlt
    intro k hk
    rw [hMbit, ← hdig k hk]
    simp only [List.mem_cons, inside, List.mem_range'_1]
    constructor
    · rintro (h | h | ⟨h1, h2, h3⟩)
      · exact ⟨Or.inl h, by rw [h]; exact hac⟩
      · exact ⟨Or.inr (Or.inl h), by rw [h]; exact hbc⟩
      · exact ⟨Or.inr (Or.inr ⟨by omega, by omega⟩), h3⟩
    · rintro ⟨h | h | ⟨h1, h2⟩, h3⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by omega, by omega, h3⟩)

/-! ### The checks -/

/-- Pieces enough for the small universe. -/
def smallPieceCount (ms : Masks) : ℕ := ms.width / pieceBits + 1

theorem lt_smallPieceCount_mul (ms : Masks) {j : ℕ} (hj : j < ms.width) :
    j < smallPieceCount ms * pieceBits := by
  unfold smallPieceCount
  have := Nat.div_add_mod ms.width pieceBits
  have := Nat.mod_lt ms.width (show 0 < pieceBits by decide)
  nlinarith

/-- The small-universe mask of a list of entries. -/
def smallMask (ms : Masks) (E : List (ℕ × ℕ)) : ℕ :=
  buildMask (resPieces (E.map Prod.swap) (smallPieceCount ms))

/-- A level's exact mask is its entries, and its entries rank at the level in
the bulk planes. -/
def levelCheck (ms : Masks) (m : ℕ) (R' : List ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (EL : List (List (ℕ × ℕ))) (r : ℕ) : Bool :=
  ((wl.getD r (0, [])).1 == smallMask ms (EL.getD r [])) &&
  ((buildMask (resPieces (EL.getD r []) (pieceCount m)) &&&
      ((2 ^ 3 ^ m - 1) ^^^ valMask m R' (r + 1))) == 0)

/-- The union of the levels' exact masks. -/
def levelUnion (wl : List (ℕ × List (EdgePerm × ℕ))) : ℕ :=
  wl.foldr (fun ent acc => ent.1 ||| acc) 0

/-- A settling mask maps into the bulk one, entry by entry. -/
def okCheck (ms : Masks) (m : ℕ) (E : List (ℕ × ℕ)) (okS okB : ℕ) : Bool :=
  let PS := pieces okS (smallPieceCount ms)
  let PB := pieces okB (pieceCount m)
  E.all fun e => !(memPiece PS e.1) || memPiece PB e.2

/-- Every pair's settling mask, as one boolean. -/
def allOk (ms : Masks) (m : ℕ) (E : List (ℕ × ℕ)) (ok : ℕ → ℕ → ℕ) (R' H' : List ℕ) : Bool :=
  (pairList m).all fun qp => okCheck ms m E (ok qp.1 qp.2) (okBig m qp.1 qp.2 R' H')

/-! ### List bookkeeping -/

theorem getD_mem {α : Type*} (d : α) : ∀ (l : List α) (r : ℕ), r < l.length → l.getD r d ∈ l := by
  intro l
  induction l with
  | nil => intro r h; simp at h
  | cons x l ih =>
    intro r h
    cases r with
    | zero => exact List.mem_cons_self
    | succ r => exact List.mem_cons_of_mem _ (ih r (by simpa using h))

theorem exists_getD_of_mem {α : Type*} (d : α) :
    ∀ (l : List α) (x : α), x ∈ l → ∃ r, r < l.length ∧ l.getD r d = x := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons y l ih =>
    intro x h
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨r, hr, hx⟩ := ih x h
      exact ⟨r + 1, by simpa using hr, hx⟩

theorem length_buildRank : ∀ (acc : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ))),
    (Masks.buildRank acc wl).length = wl.length := by
  intro acc wl
  induction wl generalizing acc with
  | nil => rfl
  | cons ent wl ih => obtain ⟨e, ws⟩ := ent; simp [Masks.buildRank, ih]

theorem getD_buildRank_fst : ∀ (acc : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ))) (r : ℕ),
    ((Masks.buildRank acc wl).getD r (0, 0)).1 = (wl.getD r (0, [])).1 := by
  intro acc wl
  induction wl generalizing acc with
  | nil => intro r; cases r <;> rfl
  | cons ent wl ih =>
    intro r
    obtain ⟨e, ws⟩ := ent
    cases r with
    | zero => rfl
    | succ r => simp only [Masks.buildRank, List.getD_cons_succ]; exact ih _ r

theorem testBit_levelUnion (wl : List (ℕ × List (EdgePerm × ℕ))) (i : ℕ) :
    (levelUnion wl).testBit i = true ↔ ∃ ent ∈ wl, ent.1.testBit i = true := by
  unfold levelUnion
  induction wl with
  | nil => simp
  | cons ent wl ih =>
    simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨e, he, h⟩)
      · exact ⟨ent, Or.inl rfl, h⟩
      · exact ⟨e, Or.inr he, h⟩
    · rintro ⟨e, rfl | he, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, he, h⟩

/-- An entry's bulk index is set in the mask built from the entries. -/
theorem testBit_buildMask_resPieces_of_mem {E : List (ℕ × ℕ)} {k : ℕ} {e : ℕ × ℕ}
    (he : e ∈ E) (hk : e.2 < k * pieceBits) :
    (buildMask (resPieces E k)).testBit e.2 = true := by
  have hL : ∀ ks ∈ resPieces E k, ∀ x ∈ ks, x < pieceBits := by
    intro ks hks x hx
    unfold resPieces at hks
    rw [List.mem_map] at hks
    obtain ⟨c, -, rfl⟩ := hks
    rw [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by decide)
  have hpos : 0 < pieceBits := by decide
  have hdecomp : e.2 = e.2 / pieceBits * pieceBits + e.2 % pieceBits :=
    (Nat.div_add_mod' e.2 pieceBits).symm
  have hc : e.2 / pieceBits < k := by rw [Nat.div_lt_iff_lt_mul hpos]; exact hk
  rw [hdecomp, testBit_buildMask _ hL _ _ (Nat.mod_lt _ hpos), decide_eq_true_eq]
  unfold resPieces
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  simp only [Option.map_some, Option.getD_some, List.mem_map, List.mem_filter, beq_iff_eq]
  exact ⟨e, ⟨he, rfl⟩, rfl⟩

/-- A witness level's masks name, for every index set, a trace whose permutation
is an entry of that level: read off in the bulk space. -/
def witCheck (ms : Masks) (m : ℕ) (wl : List (ℕ × List (EdgePerm × ℕ)))
    (EL : List (List (ℕ × ℕ))) (r : ℕ) : Bool :=
  let P := pieces (buildMask (resPieces (EL.getD r []) (pieceCount m))) (pieceCount m)
  (wl.getD r (0, [])).2.all fun gm =>
    (List.range ms.width).all fun j =>
      !gm.2.testBit j || (memPiece P (permIdx gm.1 m (bigOf ms m j)) && lastOk ms m j)

/-- What `witCheck` yields: the witness permutes into the level. -/
theorem atLevel_of_witCheck (ms : Masks) (hc : ms.Consistent) {m : ℕ} (hlen : ms.len = m + 1)
    (wl : List (ℕ × List (EdgePerm × ℕ))) (EL : List (List (ℕ × ℕ))) (certMask : ℕ) (r : ℕ)
    (hsmall : (wl.getD r (0, [])).1 = smallMask ms (EL.getD r []))
    (hentry : ∀ e ∈ EL.getD r [], e.1 < ms.width ∧ certMask.testBit e.1 = true ∧
      traceOf m e.2 = ms.traceOf e.1)
    (h : witCheck ms m wl EL r = true) :
    ∀ gm ∈ (wl.getD r (0, [])).2, ∀ i, i < ms.width → gm.2.testBit i = true →
      ms.AtLevel certMask (wl.getD r (0, [])).1 ((ms.traceOf i).map gm.1) := by
  intro gm hgm i hi hb
  unfold witCheck at h
  rw [List.all_eq_true] at h
  have h := h gm hgm
  rw [List.all_eq_true] at h
  have h := h i (List.mem_range.mpr hi)
  simp only [hb, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨hmem, hlast⟩ := h
  have hpl : permIdx gm.1 m (bigOf ms m i) < 3 ^ m := permIdx_lt _ (bigOf_lt ms m i)
  rw [memPiece_pieces _ _ _ (lt_pieceCount_mul hpl)] at hmem
  obtain ⟨e, he, hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hpl) hmem
  obtain ⟨hew, hecert, htr⟩ := hentry e he
  refine ⟨e.1, hew, hecert, ?_, ?_⟩
  · rw [hsmall]
    unfold smallMask
    have hmem' : e.swap ∈ (EL.getD r []).map Prod.swap := List.mem_map_of_mem he
    have := testBit_buildMask_resPieces_of_mem hmem' (by
      show e.1 < smallPieceCount ms * pieceBits
      exact lt_smallPieceCount_mul ms hew)
    exact this
  · rw [← htr, hej, traceOf_permIdx, traceOf_bigOf ms hc hlen hi hlast]

/-! ### The theorem -/

/-- **C-reducibility from the bulk certificate and a chord-aware residual walk.** -/
theorem cfReducible_of_hybridC (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
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
    -- the free witnesses
    (chunk nch : ℕ) (hchunk : 0 < chunk) (hcov : ms.width ≤ nch * chunk)
    (hfree : ∀ k, k < nch → freeCheck ms m (knownMask m R) goodMask (k * chunk) chunk = true)
    -- the entries, by level
    (EL : List (List (ℕ × ℕ))) (hEL : EL.length = wl.length)
    (E : List (ℕ × ℕ)) (hEdef : E = EL.flatten)
    (hE : resCheck ms m certMask E = true)
    (hU : certMask = levelUnion wl)
    -- the residual rank planes
    (R' H' : List ℕ) (hH' : H' = minPerm m R') (htop : wl.length + 1 < rankTop R')
    (hlev : ∀ r, r < wl.length → levelCheck ms m R' wl EL r = true)
    (hwitB : ∀ r, r < wl.length → witCheck ms m wl EL r = true)
    (hzero : (zeroMask m R' &&& ((2 ^ 3 ^ m - 1) ^^^ knownMask m R)) == 0)
    (hnz : (nonZero m R' &&&
      ((2 ^ 3 ^ m - 1) ^^^ buildMask (resPieces E (pieceCount m)))) == 0)
    (hok : allOk ms m E ok R' H' = true)
    (hctr : contractCheckH cf m R (buildMask (resPieces E (pieceCount m))) = true) :
    CfReducible cf := by
  set P₀ := (cfmap cf).map.RingTrace ((cfmap cf).cpring.rotate 1) with hP₀
  have hknown := known_coclosure cf m hcf R H C hlenH hClen hH hgood hchoice hpairs
  have hc : ms.Consistent := ms.consistent_of_check hchk
  subst hEdef
  set E := EL.flatten with hEdef
  -- free witnesses are in the co-closure
  have hgoodP : ∀ j, j < ms.width → goodMask.testBit j = true → KempeCoclosure P₀ (ms.traceOf j) := by
    intro j hj hgj
    have hk : j / chunk < nch := by
      rw [Nat.div_lt_iff_lt_mul hchunk]; omega
    have h := hfree (j / chunk) hk
    unfold freeCheck at h
    rw [List.all_eq_true] at h
    have hmem : j ∈ List.range' (j / chunk * chunk) chunk := by
      rw [List.mem_range'_1]
      have := Nat.div_add_mod j chunk
      have := Nat.mod_lt j hchunk
      constructor <;> nlinarith [Nat.div_mul_le_self j chunk]
    have := h j hmem
    simp only [hgj, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    obtain ⟨hmem, hlast⟩ := this
    rw [memPiece_pieces _ _ _ (lt_pieceCount_mul (bigOf_lt ms m j))] at hmem
    rw [← traceOf_bigOf ms hc hlen hj hlast]
    exact hknown _ (bigOf_lt ms m j) hmem
  -- what the entry list says of an entry
  have hentry : ∀ e ∈ E, e.1 < ms.width ∧ certMask.testBit e.1 = true ∧
      bigOf ms m e.1 = e.2 ∧ traceOf m e.2 = ms.traceOf e.1 := by
    intro e he
    unfold resCheck at hE
    rw [List.all_eq_true] at hE
    have := hE e he
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨hew, hecert⟩, hebig⟩, helast⟩ := this
    exact ⟨hew, hecert, hebig, by rw [← hebig]; exact traceOf_bigOf ms hc hlen hew helast⟩
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
  -- the certified traces are known or entries, up to permutation: the two bulk-side facts
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
      exact atLevel_of_witCheck ms hc hlen wl EL certMask r hl.1
        (fun e he => let h := hentry e (hsub r hr e he); ⟨h.1, h.2.1, h.2.2.2⟩)
        (hwitB r hr) gm (by rw [hget]; exact hgm) i hi hb)
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
    -- the entry
    obtain ⟨r, hr, hb⟩ := hlevel i hi hci
    obtain ⟨e, he, rfl⟩ := hlevelE r hr i hb hi
    have heE := hsub r hr e he
    obtain ⟨-, -, hbig, htr⟩ := hentry e heE
    have hbiglt : e.2 < 3 ^ m := by rw [← hbig]; exact bigOf_lt ms m e.1
    -- the chord is a pair
    have hchord := chord_facts (by rw [← htr] at hmw; exact hmw) hcs hqp
    have hqlt : q < p := hchord.1
    have hpm : p ≤ m := by have := hchord.2.1; rw [length_traceOf] at this; omega
    -- the settling mask maps into the bulk one
    have hokB : (okBig m q p R' H').testBit e.2 = true := by
      unfold allOk at hok
      rw [List.all_eq_true] at hok
      have h := hok (q, p) (mem_pairList.mpr ⟨hqlt, hpm⟩)
      unfold okCheck at h
      rw [List.all_eq_true] at h
      have h := h e heE
      rw [memPiece_pieces _ _ _ (lt_smallPieceCount_mul ms hi),
        memPiece_pieces _ _ _ (lt_pieceCount_mul hbiglt), hokb] at h
      simpa using h
    -- the witness, in the bulk space
    have hvtop : val R' e.2 < rankTop R' := by rw [hval r hr e he]; omega
    obtain ⟨et', hmet', hw⟩ := witness_of_chord hH' (by rw [hH', length_minPerm]) hzero'
      hgoodAllPerm hbiglt hvtop (by rw [← htr] at hmw; exact hmw) hcs hqp hokB
    refine ⟨et', hmet', ?_⟩
    rcases hw with ⟨j, hj, hkj, rfl⟩ | ⟨g, ⟨j, hj, hpos, hjtop, hje⟩, hlt⟩
    · exact Or.inl (hknown j hj hkj)
    · refine Or.inr ⟨g, ?_, ?_⟩
      · -- the permuted witness is an entry
        have hnzj : (nonZero m R').testBit j = true := by
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
    · -- a residual entry, up to permutation
      obtain ⟨g', hg'⟩ := (testBit_permClose m _ j hjlt).mp hkn
      have hgj := permIdx_lt g' hjlt
      obtain ⟨e, heE, hej⟩ := mem_of_testBit_buildMask_resPieces (lt_pieceCount_mul hgj) hg'
      obtain ⟨hew, hecert, -, htr⟩ := hentry e heE
      have hco' : KempeCoclosure P₀ (traceOf m (permIdx g' m j)) := by
        rw [← hej, htr]
        exact hres _ ⟨e.1, hew, hecert, rfl⟩
      rw [traceOf_permIdx] at hco'
      exact kempeCoclosure_of_map g' hco'

/-! ### Splitting the checks across declarations -/

theorem resCheck_nil (ms : Masks) (m certMask : ℕ) : resCheck ms m certMask [] = true := rfl

theorem okCheck_append (ms : Masks) (m : ℕ) (E₁ E₂ : List (ℕ × ℕ)) (okS okB : ℕ) :
    okCheck ms m (E₁ ++ E₂) okS okB = (okCheck ms m E₁ okS okB && okCheck ms m E₂ okS okB) := by
  unfold okCheck
  rw [List.all_append]

end Bulk
end FourColor

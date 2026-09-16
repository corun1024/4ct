import FourColor.Bulk.Pair
import FourColor.Bulk.Chords

/-!
# Toggled indices are flipped traces

The pair check speaks about indices toggled at lists of positions (`togIdxs`);
the chord lemmas speak about traces flipped by a bit mask (`flipFromB`).  This
file identifies the two: toggling the stored digits at the positions of `L`
gives the index of `flipFromB M 0 (traceOf m i)` for any mask `M` agreeing with
`L` on the stored positions, *provided the flipped trace sums to zero* — which
is the case whenever it matches a chromogram.  The completing colour then takes
care of itself.

It also provides the small bridges the assembly needs: reading a trace back to
its index, the count of non-`c1` positions strictly between two positions in
the form `partner_exists` states it, and the decoding of the choice planes.
-/

namespace FourColor
namespace Bulk

open Color

/-! ### Digits of a toggled index -/

theorem digit_togIdxs_of_nodup {m : ℕ} (L : List ℕ) (hL : L.Nodup) (i k : ℕ) :
    digit k (togIdxs m L i) =
      if k ∈ L ∧ k < m then
        (if digit k i = 1 then 2 else if digit k i = 2 then 1 else 0)
      else digit k i := by
  induction L generalizing i with
  | nil => simp [togIdxs]
  | cons r L ih =>
    have hr : r ∉ L := (List.nodup_cons.mp hL).1
    have hL' : L.Nodup := (List.nodup_cons.mp hL).2
    simp only [togIdxs]
    by_cases hrm : r < m
    · rw [if_pos hrm]
      by_cases hkr : k = r
      · subst hkr
        rw [digit_togIdx_self, ih hL' i]
        simp [hr, hrm]
      · rw [digit_togIdx_of_ne hkr, ih hL' i]
        by_cases hkL : k ∈ L
        · simp [hkL, hkr]
        · simp [hkL, hkr]
    · rw [if_neg hrm, ih hL' i]
      by_cases hkr : k = r
      · subst hkr; simp [hr, hrm]
      · by_cases hkL : k ∈ L <;> simp [hkL, hkr]

theorem colourOfDigit_swap (d : ℕ) (hd : d < 3) :
    colourOfDigit (if d = 1 then 2 else if d = 2 then 1 else 0) = flipC true (colourOfDigit d) := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> rfl

/-- The stored colours of a toggled index are the flipped colours.  The mask may
omit positions of `L` holding `c1`, where a toggle does nothing anyway. -/
theorem getD_partialOf_togIdxs {m : ℕ} (L : List ℕ) (hL : L.Nodup) (i k : ℕ) (hk : k < m)
    (M : ℕ) (hM : ∀ k, k < m → (M.testBit k = true ↔ (k ∈ L ∧ digit k i ≠ 0))) :
    (partialOf m (togIdxs m L i)).getD k 0 = flipC (M.testBit k) ((partialOf m i).getD k 0) := by
  have e : ∀ j, (partialOf m j).getD k 0 = colourOfDigit (digit k j) := by
    intro j
    rw [List.getD_eq_getElem?_getD]
    simp [partialOf, hk]
  rw [e, e, digit_togIdxs_of_nodup L hL]
  by_cases hkL : k ∈ L
  · by_cases hd0 : digit k i = 0
    · have : M.testBit k = false := by
        cases h : M.testBit k
        · rfl
        · exact absurd hd0 ((hM k hk).mp h).2
      rw [this]
      simp [hkL, hk, hd0, flipC, colourOfDigit]
    · have : M.testBit k = true := (hM k hk).mpr ⟨hkL, hd0⟩
      rw [this]
      simp only [hkL, hk, and_self, ↓reduceIte]
      exact colourOfDigit_swap _ (digit_lt k i)
  · have : M.testBit k = false := by
      cases h : M.testBit k
      · rfl
      · exact absurd ((hM k hk).mp h).1 hkL
    rw [this]
    simp [hkL, flipC]

/-- A list of length `m + 1` summing to zero is the completion of its first `m` entries. -/
theorem eq_completeTrace_take {l : List Color} {m : ℕ} (hl : l.length = m + 1) (hs : l.sum = 0) :
    l = completeTrace (l.take m) := by
  obtain ⟨l', x, rfl⟩ : ∃ l' x, l = l' ++ [x] := by
    cases h : l.reverse with
    | nil => simp at h; subst h; simp at hl
    | cons x t => exact ⟨t.reverse, x, by rw [← List.reverse_reverse l, h]; simp⟩
  have hlen : l'.length = m := by simpa using hl
  rw [List.sum_append, List.sum_singleton] at hs
  have hx : x = l'.sum := (Color.add_eq_zero_iff.mp hs).symm
  rw [List.take_left' hlen, completeTrace, hx]

/-- **Toggling is flipping.**  If the flipped trace sums to zero, its index is the
toggled index. -/
theorem traceOf_togIdxs {m : ℕ} (L : List ℕ) (hL : L.Nodup) (i : ℕ) (M : ℕ)
    (hM : ∀ k, k < m → (M.testBit k = true ↔ (k ∈ L ∧ digit k i ≠ 0)))
    (hsum : (flipFromB M 0 (traceOf m i)).sum = 0) :
    traceOf m (togIdxs m L i) = flipFromB M 0 (traceOf m i) := by
  have hlen : (flipFromB M 0 (traceOf m i)).length = m + 1 := by simp
  rw [eq_completeTrace_take hlen hsum, traceOf]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    have hk : k < m := by simpa using hk1
    have h1 : (partialOf m (togIdxs m L i))[k] = (partialOf m (togIdxs m L i)).getD k 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]; rfl
    have h2 : ((flipFromB M 0 (traceOf m i)).take m)[k] =
        (flipFromB M 0 (traceOf m i)).getD k 0 := by
      rw [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
      rfl
    rw [h1, h2, getD_flipFrom, getD_partialOf_togIdxs L hL i k hk M hM]
    simp only [length_traceOf, Nat.zero_add]
    rw [if_pos (by omega)]
    congr 1
    show (partialOf m i).getD k 0 = (traceOf m i).getD k 0
    rw [traceOf, completeTrace, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hk)]

/-! ### Reading a trace back -/

/-- The digit of a colour: `c1 ↦ 0`, `c2 ↦ 1`, `c3 ↦ 2`. -/
def digitOfColour : Color → ℕ
  | c2 => 1
  | c3 => 2
  | _ => 0

theorem digitOfColour_colourOfDigit (d : ℕ) (hd : d < 3) : digitOfColour (colourOfDigit d) = d := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> rfl

/-- The index whose first `m` colours are those of `et`. -/
def indexOf (m : ℕ) (et : List Color) : ℕ :=
  (List.range m).foldr (fun k acc => digitOfColour (et.getD k 0) * 3 ^ k + acc) 0

theorem mod_pow_succ_eq (p i : ℕ) : i % 3 ^ (p + 1) = digit p i * 3 ^ p + i % 3 ^ p := by
  conv_lhs => rw [decomp p i]
  rw [Nat.pow_succ,
    show i / (3 ^ p * 3) * (3 ^ p * 3) + digit p i * 3 ^ p + i % 3 ^ p
      = (digit p i * 3 ^ p + i % 3 ^ p) + i / (3 ^ p * 3) * (3 ^ p * 3) by ring,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  have := digit_lt p i
  have := Nat.mod_lt i (show 0 < 3 ^ p by positivity)
  have := Nat.mul_le_mul_right (3 ^ p) (show digit p i ≤ 2 by omega)
  omega

theorem indexOf_traceOf (m i : ℕ) (hi : i < 3 ^ m) : indexOf m (traceOf m i) = i := by
  -- both sides have the same digits
  suffices key : ∀ M, M ≤ m →
      (List.range M).foldr (fun k acc => digitOfColour ((traceOf m i).getD k 0) * 3 ^ k + acc) 0
        = i % 3 ^ M by
    unfold indexOf
    rw [key m le_rfl, Nat.mod_eq_of_lt hi]
  intro M
  induction M with
  | zero => intro _; simp [Nat.mod_one]
  | succ M ih =>
    intro hM
    have hfold : ∀ (l : List ℕ) (c : ℕ),
        l.foldr (fun k acc => digitOfColour ((traceOf m i).getD k 0) * 3 ^ k + acc) c =
        l.foldr (fun k acc => digitOfColour ((traceOf m i).getD k 0) * 3 ^ k + acc) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons x l ihl => rw [List.foldr_cons, List.foldr_cons, ihl]; ring
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero, hfold,
      ih (by omega), getD_traceOf_lt (by omega), digitOfColour_colourOfDigit _ (digit_lt M i),
      mod_pow_succ_eq]
    ring

theorem traceOf_injective {m i j : ℕ} (hi : i < 3 ^ m) (hj : j < 3 ^ m)
    (h : traceOf m i = traceOf m j) : i = j := by
  rw [← indexOf_traceOf m i hi, ← indexOf_traceOf m j hj, h]

/-! ### The count of non-`c1` positions between two ends -/

theorem filter_range_between {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (P : ℕ → Prop)
    [DecidablePred P] :
    ((List.range n).filter fun r => a < r ∧ r < b ∧ P r).length =
      ((List.range' (a + 1) (b - a - 1)).filter fun r => P r).length := by
  by_cases hab' : a + 1 ≤ b
  · have e : List.range n = List.range' 0 (a + 1) ++ List.range' (a + 1) (b - a - 1) ++
        List.range' b (n - b) := by
      rw [List.range_eq_range']
      have h1 := @List.range'_append_1 0 (a + 1) (b - a - 1)
      rw [Nat.zero_add, show a + 1 + (b - a - 1) = b by omega] at h1
      have h2 := @List.range'_append_1 0 b (n - b)
      rw [Nat.zero_add, show b + (n - b) = n by omega] at h2
      rw [← h2, ← h1]
    rw [e, List.filter_append, List.filter_append, List.length_append, List.length_append]
    have z1 : ((List.range' 0 (a + 1)).filter fun r => a < r ∧ r < b ∧ P r) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      rw [List.mem_range'_1] at hr
      simp; omega
    have z3 : ((List.range' b (n - b)).filter fun r => a < r ∧ r < b ∧ P r) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      rw [List.mem_range'_1] at hr
      simp; omega
    rw [z1, z3, List.length_nil, Nat.zero_add, Nat.add_zero]
    congr 1
    apply List.filter_congr
    intro r hr
    rw [List.mem_range'_1] at hr
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨-, -, h⟩; exact h
    · intro h; exact ⟨by omega, by omega, h⟩
  · have h1 : ((List.range n).filter fun r => a < r ∧ r < b ∧ P r) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r _
      simp; omega
    have h2 : b - a - 1 = 0 := by omega
    rw [h1, h2]; rfl

/-- The pair check's count agrees with the chord lemma's count on zero-free traces. -/
theorem nonC1Count_eq {m i p q : ℕ} (hpq : p < q) (hq : q ≤ m)
    (h0 : (0 : Color) ∉ traceOf m i) :
    nonC1Count m i (p + 1) q =
      ((List.range (m + 1)).filter fun r =>
        min p q < r ∧ r < max p q ∧ (traceOf m i).getD r 0 ≠ c1).length := by
  rw [min_eq_left hpq.le, max_eq_right hpq.le, filter_range_between hpq.le (by omega)]
  unfold nonC1Count
  congr 1
  apply List.filter_congr
  intro r hr
  rw [List.mem_range'_1] at hr
  have hr' : r < (traceOf m i).length := by simp; omega
  have hmem : (traceOf m i).getD r 0 ∈ traceOf m i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']
    exact List.getElem_mem _
  have hne0 : (traceOf m i).getD r 0 ≠ 0 := fun h => h0 (h ▸ hmem)
  simp only [decide_eq_decide]
  cases h : (traceOf m i).getD r 0 <;> simp_all

/-! ### Choice planes -/

/-- The choice code of trace `i`: the position it is certified with. -/
def choiceCode (C : List ℕ) (i : ℕ) : ℕ := val C i

/-- The traces whose choice code is `p`, among those in `cert`. -/
def choiceMask (m : ℕ) (C : List ℕ) (cert : ℕ) (p : ℕ) : ℕ :=
  (List.range C.length).foldr
    (fun b acc => acc &&& (if (p >>> b) % 2 = 1 then C.getD b 0 else (2 ^ 3 ^ m - 1) ^^^ C.getD b 0))
    cert

theorem val_lt_two_pow (C : List ℕ) (i : ℕ) : val C i < 2 ^ C.length := by
  induction C with
  | nil => simp [val]
  | cons a as ih =>
    simp only [val, List.length_cons, Nat.pow_succ]
    split_ifs <;> omega

theorem testBit_choiceMask {m : ℕ} (C : List ℕ) (cert p i : ℕ) (hi : i < 3 ^ m)
    (hp : p < 2 ^ C.length) :
    (choiceMask m C cert p).testBit i = (cert.testBit i && decide (val C i = p)) := by
  unfold choiceMask
  -- bits of `p` and of `val C i` agree below `C.length` exactly when the numbers agree
  suffices key : ∀ (D : List ℕ) (k : ℕ), D = C.drop k → k ≤ C.length →
      ((List.range' k (C.length - k)).foldr
        (fun b acc => acc &&& (if (p >>> b) % 2 = 1 then C.getD b 0 else (2 ^ 3 ^ m - 1) ^^^ C.getD b 0))
        cert).testBit i =
      (cert.testBit i && decide (val D i = p >>> k)) by
    have := key C 0 rfl (Nat.zero_le _)
    rw [List.range_eq_range']
    simpa using this
  intro D
  induction D with
  | nil =>
    intro k hD hk
    have hk' : k = C.length := by
      have := congrArg List.length hD; simp at this; omega
    subst hk'
    simp only [Nat.sub_self, List.range'_zero, List.foldr_nil, val]
    have : p >>> C.length = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hp
    simp [this]
  | cons a D ih =>
    intro k hD hk
    have hlen : k < C.length := by
      have := congrArg List.length hD; simp at this; omega
    have hCk : C.getD k 0 = a := by
      have h := congrArg (fun l => l[0]?) hD.symm
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h
      simp [List.getD_eq_getElem?_getD, h]
    have hD' : D = C.drop (k + 1) := by
      have : C.drop k = a :: D := hD.symm
      rw [← List.drop_drop, this]; rfl
    rw [show C.length - k = (C.length - (k + 1)) + 1 by omega, List.range'_succ, List.foldr_cons,
      Nat.testBit_and, ih (k + 1) hD' (by omega), hCk]
    have hsh : p / 2 ^ k = (if (p / 2 ^ k) % 2 = 1 then 1 else 0) + 2 * (p / 2 ^ (k + 1)) := by
      have := Nat.div_add_mod (p / 2 ^ k) 2
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      split_ifs with h <;> omega
    simp only [val, Nat.shiftRight_eq_div_pow]
    generalize hq : p / 2 ^ (k + 1) = q at hsh ⊢
    generalize hr : p / 2 ^ k = r at hsh ⊢
    by_cases hpk : r % 2 = 1
    · rw [if_pos hpk] at hsh ⊢
      rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha
      · simp only [ha, Bool.and_true, eq_self_iff_true, ↓reduceIte]
        cases hc : cert.testBit i
        · simp
        · simp only [Bool.true_and]; apply decide_eq_decide.mpr
          constructor <;> intro h <;> omega
      · simp only [ha, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        cases hc : cert.testBit i
        · simp
        · simp only [Bool.true_and, Bool.false_and]
          symm; apply decide_eq_false; omega
    · rw [if_neg hpk] at hsh ⊢
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
      rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha
      · simp only [ha, hi, decide_true, Bool.true_xor, Bool.not_true, Bool.and_false,
          eq_self_iff_true, ↓reduceIte]
        cases hc : cert.testBit i
        · simp
        · simp only [Bool.true_and, Bool.false_and]
          symm; apply decide_eq_false; omega
      · simp only [ha, hi, decide_true, Bool.true_xor, Bool.not_false, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        cases hc : cert.testBit i
        · simp
        · simp only [Bool.true_and]; apply decide_eq_decide.mpr
          constructor <;> intro h <;> omega

end Bulk
end FourColor

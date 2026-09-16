import FourColor.Bulk.Move
import FourColor.Bulk.FoldList

/-!
# The colouring fold as a bulk bitmask computation

`finalTraces cp` (`FourColor.Bulk.FoldList`) is the list of ring traces the
colouring program `cp` enumerates.  This file computes that list *in bulk*: one
natural number whose set bits are the enumerated traces, with every
construction step realised as a handful of `move2` block moves.

The state of the computation is a triple `(M, order, S)`:

* `M` is a bitmask over indices below `3 ^ S`, one base-3 digit per slot;
* `order` lists, head first, the digit slot holding each ring position, so the
  trace an index `i` stands for is `slotTrace order i`;
* `S` is the number of slots, and `order` is always a permutation of
  `List.range S`, which makes `slotTrace order` a bijection from the indices
  below `3 ^ S` to the traces of length `S` avoiding the colour `0`.

Slots freed by the `K` and `A` steps are recycled (`recycle`), so `S` never
exceeds the current ring size; this is what keeps the masks small enough for
the kernel to run the computation.

## Main definitions

* `slotTrace order i` — the trace index `i` stands for.
* `bulkStep s`, `bulkFold cp` — one step, and a whole program, in bulk.
* `bulkFinalState rp`, `bulkFinal cp` — the bulk analogue of `finalTraces`,
  and its projection to a mask over `3 ^ m`.

## Main results

* `testBit_bulkFold` — **the exactness of the bulk fold**: the bits of the
  folded mask are exactly the traces `foldList` enumerates.
* `testBit_bulkFinal` — the projected mask holds exactly the tails of the
  traces of `finalTraces cp.reverse`.
-/

namespace FourColor
namespace Bulk

open Color EdgePerm

/-! ### Colours as digits -/

/-- The digit a colour stands for; `c0` never occurs in a trace. -/
def fdigitOf : Color → ℕ
  | .c0 => 0
  | .c1 => 0
  | .c2 => 1
  | .c3 => 2

@[simp] theorem fdigitOf_lt (c : Color) : fdigitOf c < 3 := by cases c <;> decide

theorem colourOfDigit_fdigitOf (c : Color) (h : c ≠ 0) : colourOfDigit (fdigitOf c) = c := by
  revert h; revert c; decide

theorem fdigitOf_colourOfDigit {d : ℕ} (h : d < 3) : fdigitOf (colourOfDigit d) = d := by
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> rfl

theorem colourOfDigit_inj {d e : ℕ} (hd : d < 3) (he : e < 3)
    (h : colourOfDigit d = colourOfDigit e) : d = e := by
  rw [← fdigitOf_colourOfDigit hd, ← fdigitOf_colourOfDigit he, h]

/-! ### Digits above the top slot -/

theorem digit_eq_zero_of_lt {k i : ℕ} (h : i < 3 ^ k) {s : ℕ} (hs : k ≤ s) : digit s i = 0 := by
  unfold digit
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hs))]

theorem lt_of_digit_zero {k i : ℕ} (hi : i < 3 ^ (k + 1)) (h : digit k i = 0) : i < 3 ^ k := by
  have hd := decomp k i
  rw [h, Nat.div_eq_of_lt hi] at hd
  have h2 : i % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
  omega

/-! ### The trace an index stands for -/

/-- The trace index `i` stands for: the colour of the digit in each slot of
`order`, in ring order. -/
def slotTrace (order : List ℕ) (i : ℕ) : List Color :=
  order.map fun s => colourOfDigit (digit s i)

@[simp] theorem slotTrace_nil (i : ℕ) : slotTrace [] i = [] := rfl

@[simp] theorem slotTrace_cons (s : ℕ) (os : List ℕ) (i : ℕ) :
    slotTrace (s :: os) i = colourOfDigit (digit s i) :: slotTrace os i := rfl

@[simp] theorem length_slotTrace (order : List ℕ) (i : ℕ) :
    (slotTrace order i).length = order.length := by
  simp [slotTrace]

theorem zero_notMem_slotTrace (order : List ℕ) (i : ℕ) : (0 : Color) ∉ slotTrace order i := by
  intro h
  obtain ⟨s, -, hs⟩ := List.mem_map.mp h
  exact colourOfDigit_ne_zero _ hs

theorem slotTrace_rotate (order : List ℕ) (n i : ℕ) :
    slotTrace (order.rotate n) i = (slotTrace order i).rotate n :=
  List.map_rotate _ _ _

/-- Setting a digit in a slot outside `order` does not change the trace. -/
theorem slotTrace_setDigit_of_not_mem {order : List ℕ} {s d : ℕ} (hs : s ∉ order) (hd : d < 3)
    (i : ℕ) : slotTrace order (setDigit s d i) = slotTrace order i :=
  List.map_congr_left fun r hr => by
    have hrs : r ≠ s := by rintro rfl; exact hs hr
    rw [digit_setDigit_of_ne hrs hd]

/-! ### Slot layouts

`order` is always a permutation of `List.range S`; the two facts that needs are
that every slot below `S` occurs, and that `slotTrace order` is then injective
below `3 ^ S`. -/

theorem mem_of_lt_of_nodup {order : List ℕ} {S : ℕ} (hnd : order.Nodup)
    (hlt : ∀ s ∈ order, s < S) (hlen : order.length = S) {s : ℕ} (hs : s < S) : s ∈ order := by
  classical
  have hsub : order.toFinset ⊆ Finset.range S := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simpa using hlt x hx
  have hcard : (Finset.range S).card ≤ order.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : s ∈ order.toFinset := by rw [heq]; simpa using hs
  simpa using this

theorem slotTrace_inj {order : List ℕ} {S i i' : ℕ} (hnd : order.Nodup)
    (hlt : ∀ s ∈ order, s < S) (hlen : order.length = S) (hi : i < 3 ^ S) (hi' : i' < 3 ^ S)
    (h : slotTrace order i = slotTrace order i') : i = i' := by
  refine digits_ext hi hi' fun r => ?_
  by_cases hr : r < S
  · have hmem := mem_of_lt_of_nodup hnd hlt hlen hr
    have hpt := List.map_inj_left.mp h r hmem
    exact colourOfDigit_inj (digit_lt _ _) (digit_lt _ _) hpt
  · rw [digit_eq_zero_of_lt hi (by omega), digit_eq_zero_of_lt hi' (by omega)]

/-- The index a trace stands for, built slot by slot. -/
def mkIndex : List ℕ → List Color → ℕ
  | [], _ => 0
  | _, [] => 0
  | s :: os, c :: cs => setDigit s (fdigitOf c) (mkIndex os cs)

theorem mkIndex_lt {order : List ℕ} {S : ℕ} (hlt : ∀ s ∈ order, s < S) :
    ∀ t : List Color, mkIndex order t < 3 ^ S := by
  induction order with
  | nil => intro _; change (0 : ℕ) < 3 ^ S; positivity
  | cons s os ih =>
    intro t
    cases t with
    | nil => change (0 : ℕ) < 3 ^ S; positivity
    | cons c cs =>
      exact setDigit_lt (hlt s List.mem_cons_self) (fdigitOf_lt c)
        (ih (fun r hr => hlt r (List.mem_cons_of_mem _ hr)) cs)

theorem slotTrace_mkIndex : ∀ {order : List ℕ}, order.Nodup → ∀ t : List Color,
    t.length = order.length → (0 : Color) ∉ t → slotTrace order (mkIndex order t) = t := by
  intro order
  induction order with
  | nil => intro _ t hl _; simpa using (List.length_eq_zero_iff.mp (by simpa using hl)).symm
  | cons s os ih =>
    intro hnd t hl h0
    cases t with
    | nil => simp at hl
    | cons c cs =>
      have hs : s ∉ os := (List.nodup_cons.mp hnd).1
      have hnd' : os.Nodup := (List.nodup_cons.mp hnd).2
      have hc : c ≠ 0 := fun hc0 => h0 (by simp [hc0])
      have h0' : (0 : Color) ∉ cs := fun hcs => h0 (List.mem_cons_of_mem _ hcs)
      rw [mkIndex, slotTrace_cons, digit_setDigit_self (fdigitOf_lt c),
        colourOfDigit_fdigitOf c hc, slotTrace_setDigit_of_not_mem hs (fdigitOf_lt c),
        ih hnd' cs (by simpa using hl) h0']

/-! ### Block moves outside the index range

`testBit_move2` characterises the moved block below `3 ^ m`; no bit above that
is ever set, since the source block lies below `3 ^ m` and so does its image. -/

theorem testBit_move2' {m p q v w u x : ℕ} (hp : p < m) (hq : q < m) (hpq : p ≠ q)
    (hv : v < 3) (hw : w < 3) (hu : u < 3) (hx : x < 3) (M j : ℕ) :
    (move2 m p q v w u x M).testBit j =
      (decide (j < 3 ^ m ∧ digit p j = u ∧ digit q j = x) &&
        M.testBit (setDigit p v (setDigit q w j))) := by
  by_cases hj : j < 3 ^ m
  · rw [testBit_move2 hp hq hpq hv hw hu hx M j hj]
    simp [hj]
  · have hfalse : (move2 m p q v w u x M).testBit j = false := by
      unfold move2
      rw [testBit_shiftBy]
      set δ : ℤ := (u - v : ℤ) * 3 ^ p + (x - w : ℤ) * 3 ^ q with hδ
      by_cases h0 : 0 ≤ (j : ℤ) - δ
      · rw [Nat.testBit_and, Nat.testBit_and, testBit_sel hp v hv, testBit_sel hq w hw]
        set k := ((j : ℤ) - δ).toNat with hk
        have hks : ¬ (k < 3 ^ m ∧ digit p k = v ∧ digit q k = w) := by
          rintro ⟨hklt, hkp, hkq⟩
          have h1 : (setDigit q x k : ℤ) = k + (x - w : ℤ) * 3 ^ q := setDigit_eq_add hkq
          have h2 : digit p (setDigit q x k) = v := by rw [digit_setDigit_of_ne hpq hx, hkp]
          have h3 : (setDigit p u (setDigit q x k) : ℤ)
              = setDigit q x k + (u - v : ℤ) * 3 ^ p := setDigit_eq_add h2
          have hjk : (j : ℤ) = k + δ := by rw [hk]; omega
          have hcast : (j : ℤ) = (setDigit p u (setDigit q x k) : ℤ) := by
            rw [h3, h1, hjk, hδ]; ring
          have hjj : j = setDigit p u (setDigit q x k) := by exact_mod_cast hcast
          exact hj (hjj ▸ setDigit_lt hp hu (setDigit_lt hq hx hklt))
        by_cases hkp : k < 3 ^ m ∧ digit p k = v
        · have : ¬ (k < 3 ^ m ∧ digit q k = w) := by tauto
          simp [this]
        · simp [hkp]
      · have hd0 : decide (0 ≤ (j : ℤ) - δ) = false := by
          simp only [decide_eq_false_iff_not]; exact h0
        rw [hd0, Bool.false_and]
    rw [hfalse]
    simp [hj]

/-! ### Exchanging two digit slots -/

/-- The slot `r` holds, after the exchange of `s` and `t`, what slot `tau s t r`
held before. -/
def tau (s t r : ℕ) : ℕ := if r = s then t else if r = t then s else r

theorem tau_of_ne {s t r : ℕ} (hs : r ≠ s) (ht : r ≠ t) : tau s t r = r := by
  simp [tau, hs, ht]

@[simp] theorem tau_left (s t : ℕ) : tau s t s = t := by simp [tau]

@[simp] theorem tau_right {s t : ℕ} (hst : t ≠ s) : tau s t t = s := by simp [tau, hst]

theorem tau_tau (s t r : ℕ) : tau s t (tau s t r) = r := by
  unfold tau
  split_ifs with h1 h2 h3 h4 <;> omega

/-- Index `j` with the digits in slots `s` and `t` exchanged. -/
def swapIdx (s t j : ℕ) : ℕ := setDigit s (digit t j) (setDigit t (digit s j) j)

theorem digit_swapIdx (s t r j : ℕ) :
    digit r (swapIdx s t j) = digit (tau s t r) j := by
  unfold swapIdx
  by_cases h1 : r = s
  · subst h1
    rw [digit_setDigit_self (digit_lt t j), tau_left]
  · by_cases h2 : r = t
    · have hts : t ≠ s := fun h => h1 (h2.trans h)
      rw [h2, digit_setDigit_of_ne hts (digit_lt t j), digit_setDigit_self (digit_lt s j),
        tau_right hts]
    · rw [digit_setDigit_of_ne h1 (digit_lt t j), digit_setDigit_of_ne h2 (digit_lt s j),
        tau_of_ne h1 h2]

theorem slotTrace_swapIdx (s t : ℕ) (order : List ℕ) (j : ℕ) :
    slotTrace order (swapIdx s t j) = slotTrace (order.map (tau s t)) j := by
  unfold slotTrace
  rw [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply]
  rw [digit_swapIdx]

theorem swapIdx_lt {S s t j : ℕ} (hs : s < S) (ht : t < S) (hj : j < 3 ^ S) :
    swapIdx s t j < 3 ^ S :=
  setDigit_lt hs (digit_lt _ _) (setDigit_lt ht (digit_lt _ _) hj)

/-- Exchange the digit slots `s` and `t`. -/
def swapAll (S s t M : ℕ) : ℕ :=
  move2 S s t 0 0 0 0 M ||| move2 S s t 0 1 1 0 M ||| move2 S s t 0 2 2 0 M
    ||| move2 S s t 1 0 0 1 M ||| move2 S s t 1 1 1 1 M ||| move2 S s t 1 2 2 1 M
    ||| move2 S s t 2 0 0 2 M ||| move2 S s t 2 1 1 2 M ||| move2 S s t 2 2 2 2 M

theorem testBit_swapAll {S s t : ℕ} (hs : s < S) (ht : t < S) (hst : s ≠ t) (M j : ℕ) :
    (swapAll S s t M).testBit j = (decide (j < 3 ^ S) && M.testBit (swapIdx s t j)) := by
  unfold swapAll swapIdx
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  simp only [Nat.testBit_or, testBit_move2' hs ht hst, e0, e1, e2]
  rcases (show digit s j = 0 ∨ digit s j = 1 ∨ digit s j = 2 by have := digit_lt s j; omega)
    with h1 | h1 | h1 <;>
  rcases (show digit t j = 0 ∨ digit t j = 1 ∨ digit t j = 2 by have := digit_lt t j; omega)
    with h2 | h2 | h2 <;>
  simp [h1, h2]

/-- Exchange the digit slots `s` and `t`, where slot `s` holds `0` in every live
index: only the three blocks with digit `0` at `s` need moving. -/
def swap0 (S s t M : ℕ) : ℕ :=
  move2 S s t 0 0 0 0 M ||| move2 S s t 0 1 1 0 M ||| move2 S s t 0 2 2 0 M

theorem testBit_swap0 {S s t : ℕ} (hs : s < S) (ht : t < S) (hst : s ≠ t) (M j : ℕ) :
    (swap0 S s t M).testBit j =
      (decide (j < 3 ^ S ∧ digit t j = 0) && M.testBit (swapIdx s t j)) := by
  unfold swap0 swapIdx
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  simp only [Nat.testBit_or, testBit_move2' hs ht hst, e0, e1, e2]
  rcases (show digit s j = 0 ∨ digit s j = 1 ∨ digit s j = 2 by have := digit_lt s j; omega)
    with h1 | h1 | h1 <;>
  rcases (show digit t j = 0 ∨ digit t j = 1 ∨ digit t j = 2 by have := digit_lt t j; omega)
    with h2 | h2 | h2 <;>
  simp [h1, h2]

/-! ### The state of the bulk computation

A state `(M, order, S)` is *good* when `order` is a permutation of
`List.range S` and `M` is a mask over the indices below `3 ^ S`.  Being a
permutation of `List.range S` is what makes `slotTrace order` injective on
those indices. -/

/-- The invariant of a bulk state. -/
structure Good (M : ℕ) (order : List ℕ) (S : ℕ) : Prop where
  /-- No slot is used twice. -/
  nodup : order.Nodup
  /-- Every slot is below `S`. -/
  slot_lt : ∀ s ∈ order, s < S
  /-- There are exactly `S` slots, so every slot below `S` is used. -/
  len : order.length = S
  /-- The ring is nonempty. -/
  pos : 1 ≤ S
  /-- Every live index is below `3 ^ S`. -/
  bit_lt : ∀ i, M.testBit i = true → i < 3 ^ S

theorem Good.mem_of_lt {M : ℕ} {order : List ℕ} {S : ℕ} (h : Good M order S) {s : ℕ}
    (hs : s < S) : s ∈ order := mem_of_lt_of_nodup h.nodup h.slot_lt h.len hs

theorem Good.inj {M : ℕ} {order : List ℕ} {S i i' : ℕ} (h : Good M order S)
    (hi : i < 3 ^ S) (hi' : i' < 3 ^ S) (he : slotTrace order i = slotTrace order i') : i = i' :=
  slotTrace_inj h.nodup h.slot_lt h.len hi hi' he

/-- `testBit_move2` in propositional form. -/
theorem testBit_move2_iff {m p q v w u x : ℕ} (hp : p < m) (hq : q < m) (hpq : p ≠ q)
    (hv : v < 3) (hw : w < 3) (hu : u < 3) (hx : x < 3) (M j : ℕ) :
    (move2 m p q v w u x M).testBit j = true ↔
      (j < 3 ^ m ∧ digit p j = u ∧ digit q j = x) ∧
        M.testBit (setDigit p v (setDigit q w j)) = true := by
  rw [testBit_move2' hp hq hpq hv hw hu hx, Bool.and_eq_true, decide_eq_true_eq]

/-! ### The `U` step

Two fresh slots `S`, `S + 1` receive a repeated colour. -/

/-- The `U` step: a new pair of equal colours in the two fresh slots. -/
def stepU (S M : ℕ) : ℕ :=
  move2 (S + 2) S (S + 1) 0 0 0 0 M ||| move2 (S + 2) S (S + 1) 0 0 1 1 M
    ||| move2 (S + 2) S (S + 1) 0 0 2 2 M

theorem testBit_stepU (S M j : ℕ) :
    (stepU S M).testBit j = true ↔
      j < 3 ^ (S + 2) ∧ digit S j = digit (S + 1) j ∧
        M.testBit (setDigit S 0 (setDigit (S + 1) 0 j)) = true := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hp : S < S + 2 := by omega
  have hq : S + 1 < S + 2 := by omega
  have hpq : S ≠ S + 1 := by omega
  unfold stepU
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hp hq hpq, e0, e1, e2]
  have hd1 := digit_lt S j
  have hd2 := digit_lt (S + 1) j
  constructor
  · rintro ((⟨⟨a, b, c⟩, d⟩ | ⟨⟨a, b, c⟩, d⟩) | ⟨⟨a, b, c⟩, d⟩) <;> exact ⟨a, by omega, d⟩
  · rintro ⟨a, b, c⟩
    rcases (show digit S j = 0 ∨ digit S j = 1 ∨ digit S j = 2 by omega) with h | h | h
    · exact Or.inl (Or.inl ⟨⟨a, h, by omega⟩, c⟩)
    · exact Or.inl (Or.inr ⟨⟨a, h, by omega⟩, c⟩)
    · exact Or.inr ⟨⟨a, h, by omega⟩, c⟩

theorem stepU_spec {M : ℕ} {order : List ℕ} {S : ℕ} (hgood : Good M order S)
    (j : ℕ) (hj : j < 3 ^ (S + 2)) :
    ((stepU S M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧
        slotTrace (S :: (S + 1) :: order) j ∈ enum1 .U (slotTrace order i)) := by
  have hSo : S ∉ order := fun h => absurd (hgood.slot_lt S h) (by omega)
  have hS1o : S + 1 ∉ order := fun h => absurd (hgood.slot_lt _ h) (by omega)
  have hsrc : slotTrace order (setDigit S 0 (setDigit (S + 1) 0 j)) = slotTrace order j := by
    rw [slotTrace_setDigit_of_not_mem hSo (by norm_num),
      slotTrace_setDigit_of_not_mem hS1o (by norm_num)]
  have hsrclt : setDigit S 0 (setDigit (S + 1) 0 j) < 3 ^ S := by
    refine lt_of_digit_zero (k := S) (lt_of_digit_zero (k := S + 1) ?_ ?_) ?_
    · exact setDigit_lt (by omega) (by norm_num) (setDigit_lt (by omega) (by norm_num) hj)
    · rw [digit_setDigit_of_ne (by omega) (by norm_num), digit_setDigit_self (by norm_num)]
    · rw [digit_setDigit_self (by norm_num)]
  rw [testBit_stepU]
  constructor
  · rintro ⟨-, heq, hb⟩
    refine ⟨_, hb, ?_⟩
    rw [hsrc, slotTrace_cons, slotTrace_cons, heq, enum1_U]
    rcases (show digit (S + 1) j = 0 ∨ digit (S + 1) j = 1 ∨ digit (S + 1) j = 2 by
      have := digit_lt (S + 1) j; omega) with h | h | h <;> rw [h]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    rw [enum1_U] at hmem
    simp only [slotTrace_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at hmem
    have hstep : ∀ c : Color, colourOfDigit (digit S j) = c → colourOfDigit (digit (S + 1) j) = c →
        slotTrace order j = slotTrace order i →
        j < 3 ^ (S + 2) ∧ digit S j = digit (S + 1) j ∧
          M.testBit (setDigit S 0 (setDigit (S + 1) 0 j)) = true := by
      intro c h1 h2 h3
      have heq : digit S j = digit (S + 1) j :=
        colourOfDigit_inj (digit_lt _ _) (digit_lt _ _) (by rw [h1, h2])
      refine ⟨hj, heq, ?_⟩
      have : setDigit S 0 (setDigit (S + 1) 0 j) = i :=
        hgood.inj hsrclt hi3 (by rw [hsrc, h3])
      rw [this]; exact hbi
    rcases hmem with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact hstep _ h1 h2 h3
    · exact hstep _ h1 h2 h3
    · exact hstep _ h1 h2 h3

/-! ### The `Y` step

The head slot keeps the ring position, a fresh slot `S` is inserted after it,
and the two receive the two nontrivial rotations of the old colour. -/

/-- The `Y` step: the head colour `v` becomes `e231 v, e312 v` or
`e312 v, e231 v` in the head slot and the fresh slot `S`. -/
def stepY (S s0 M : ℕ) : ℕ :=
  move2 (S + 1) s0 S 0 0 1 2 M ||| move2 (S + 1) s0 S 0 0 2 1 M
    ||| move2 (S + 1) s0 S 1 0 2 0 M ||| move2 (S + 1) s0 S 1 0 0 2 M
    ||| move2 (S + 1) s0 S 2 0 0 1 M ||| move2 (S + 1) s0 S 2 0 1 0 M

theorem stepY_spec {M s0 S : ℕ} {rest : List ℕ} (hgood : Good M (s0 :: rest) S)
    (j : ℕ) (hj : j < 3 ^ (S + 1)) :
    ((stepY S s0 M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: S :: rest) j ∈ enum1 .Y (slotTrace (s0 :: rest) i)) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs0r : s0 ∉ rest := (List.nodup_cons.mp hgood.nodup).1
  have hSr : S ∉ rest := fun h => absurd (hgood.slot_lt S (List.mem_cons_of_mem _ h)) (by omega)
  have hne : s0 ≠ S := by omega
  have hp : s0 < S + 1 := by omega
  have hq : S < S + 1 := by omega
  have hsrc : ∀ v : ℕ, v < 3 → slotTrace (s0 :: rest) (setDigit s0 v (setDigit S 0 j))
      = colourOfDigit v :: slotTrace rest j := by
    intro v hv
    rw [slotTrace_cons, digit_setDigit_self hv, slotTrace_setDigit_of_not_mem hs0r hv,
      slotTrace_setDigit_of_not_mem hSr (by norm_num)]
  have hsrclt : ∀ v : ℕ, v < 3 → setDigit s0 v (setDigit S 0 j) < 3 ^ S := by
    intro v hv
    refine lt_of_digit_zero (k := S) ?_ ?_
    · exact setDigit_lt hp hv (setDigit_lt hq (by norm_num) hj)
    · rw [digit_setDigit_of_ne (by omega) hv, digit_setDigit_self (by norm_num)]
  have key : ∀ v u x : ℕ, v < 3 → digit s0 j = u → digit S j = x →
      (colourOfDigit u :: colourOfDigit x :: slotTrace rest j) ∈
        enum1 .Y (colourOfDigit v :: slotTrace rest j) →
      M.testBit (setDigit s0 v (setDigit S 0 j)) = true →
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: S :: rest) j ∈ enum1 .Y (slotTrace (s0 :: rest) i) := by
    intro v u x hv h1 h2 hmem hb
    exact ⟨_, hb, by rw [hsrc v hv, slotTrace_cons, slotTrace_cons, h1, h2]; exact hmem⟩
  unfold stepY
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hp hq hne, e0, e1, e2]
  constructor
  · rintro (((((⟨⟨-, h1, h2⟩, hb⟩ | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) |
      ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩)
    · exact key 0 1 2 e0 h1 h2 List.mem_cons_self hb
    · exact key 0 2 1 e0 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
    · exact key 1 2 0 e1 h1 h2 List.mem_cons_self hb
    · exact key 1 0 2 e1 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
    · exact key 2 0 1 e2 h1 h2 List.mem_cons_self hb
    · exact key 2 1 0 e2 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    have hv3 : digit s0 i < 3 := digit_lt _ _
    rw [slotTrace_cons, enum1_Y_cons] at hmem
    simp only [slotTrace_cons, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at hmem
    have hT : slotTrace rest j = slotTrace rest i := by
      rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
    have hb : M.testBit (setDigit s0 (digit s0 i) (setDigit S 0 j)) = true := by
      have : setDigit s0 (digit s0 i) (setDigit S 0 j) = i :=
        hgood.inj (hsrclt _ hv3) hi3 (by rw [hsrc _ hv3, slotTrace_cons, hT])
      rw [this]; exact hbi
    have hdig : ∀ (c : Color) (r : ℕ), colourOfDigit (digit r j) = c → digit r j = fdigitOf c := by
      intro c r h; rw [← h, fdigitOf_colourOfDigit (digit_lt _ _)]
    rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega) with hv | hv | hv <;>
      rw [hv] at hmem hb
    · rcases hmem with ⟨ha, hbb, -⟩ | ⟨ha, hbb, -⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩))))
    · rcases hmem with ⟨ha, hbb, -⟩ | ⟨ha, hbb, -⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩))
    · rcases hmem with ⟨ha, hbb, -⟩ | ⟨ha, hbb, -⟩
      · exact Or.inl (Or.inr ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩)
      · exact Or.inr ⟨⟨hj, hdig _ _ ha, hdig _ _ hbb⟩, hb⟩

/-! ### The `H` step

Two equal head colours are replaced by the two nontrivial rotations, and two
different head colours are exchanged; the ring positions do not move. -/

/-- The `H` step: `(v, v) ↦ (e231 v, e231 v), (e312 v, e312 v)`, and
`(v, w) ↦ (w, v)` for `v ≠ w`. -/
def stepH (S s0 s1 M : ℕ) : ℕ :=
  move2 S s0 s1 0 0 1 1 M ||| move2 S s0 s1 0 0 2 2 M
    ||| move2 S s0 s1 1 1 2 2 M ||| move2 S s0 s1 1 1 0 0 M
    ||| move2 S s0 s1 2 2 0 0 M ||| move2 S s0 s1 2 2 1 1 M
    ||| move2 S s0 s1 0 1 1 0 M ||| move2 S s0 s1 1 0 0 1 M
    ||| move2 S s0 s1 0 2 2 0 M ||| move2 S s0 s1 2 0 0 2 M
    ||| move2 S s0 s1 1 2 2 1 M ||| move2 S s0 s1 2 1 1 2 M

theorem stepH_spec {M s0 s1 S : ℕ} {rest : List ℕ} (hgood : Good M (s0 :: s1 :: rest) S)
    (j : ℕ) (hj : j < 3 ^ S) :
    ((stepH S s0 s1 M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: s1 :: rest) j ∈ enum1 .H (slotTrace (s0 :: s1 :: rest) i)) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hnd := hgood.nodup
  have hne : s0 ≠ s1 := fun h =>
    (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hs0r : s0 ∉ rest := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h)
  have hs1r : s1 ∉ rest := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 h
  have hsrc : ∀ v w : ℕ, v < 3 → w < 3 →
      slotTrace (s0 :: s1 :: rest) (setDigit s0 v (setDigit s1 w j))
        = colourOfDigit v :: colourOfDigit w :: slotTrace rest j := by
    intro v w hv hw
    rw [slotTrace_cons, slotTrace_cons, digit_setDigit_self hv,
      digit_setDigit_of_ne (Ne.symm hne) hv, digit_setDigit_self hw,
      slotTrace_setDigit_of_not_mem hs0r hv, slotTrace_setDigit_of_not_mem hs1r hw]
  have hsrclt : ∀ v w : ℕ, v < 3 → w < 3 → setDigit s0 v (setDigit s1 w j) < 3 ^ S :=
    fun v w hv hw => setDigit_lt hs0 hv (setDigit_lt hs1 hw hj)
  have key : ∀ v w u x : ℕ, v < 3 → w < 3 → digit s0 j = u → digit s1 j = x →
      (colourOfDigit u :: colourOfDigit x :: slotTrace rest j) ∈
        enum1 .H (colourOfDigit v :: colourOfDigit w :: slotTrace rest j) →
      M.testBit (setDigit s0 v (setDigit s1 w j)) = true →
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: s1 :: rest) j ∈ enum1 .H (slotTrace (s0 :: s1 :: rest) i) :=
    fun v w u x hv hw h1 h2 hmem hb =>
      ⟨_, hb, by rw [hsrc v w hv hw, slotTrace_cons, slotTrace_cons, h1, h2]; exact hmem⟩
  unfold stepH
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2]
  constructor
  · rintro (((((((((((⟨⟨-, h1, h2⟩, hb⟩ | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩,
      hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) |
      ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩)
    · exact key 0 0 1 1 e0 e0 h1 h2 List.mem_cons_self hb
    · exact key 0 0 2 2 e0 e0 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
    · exact key 1 1 2 2 e1 e1 h1 h2 List.mem_cons_self hb
    · exact key 1 1 0 0 e1 e1 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
    · exact key 2 2 0 0 e2 e2 h1 h2 List.mem_cons_self hb
    · exact key 2 2 1 1 e2 e2 h1 h2 (List.mem_cons_of_mem _ List.mem_cons_self) hb
    · exact key 0 1 1 0 e0 e1 h1 h2 List.mem_cons_self hb
    · exact key 1 0 0 1 e1 e0 h1 h2 List.mem_cons_self hb
    · exact key 0 2 2 0 e0 e2 h1 h2 List.mem_cons_self hb
    · exact key 2 0 0 2 e2 e0 h1 h2 List.mem_cons_self hb
    · exact key 1 2 2 1 e1 e2 h1 h2 List.mem_cons_self hb
    · exact key 2 1 1 2 e2 e1 h1 h2 List.mem_cons_self hb
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    have hv3 : digit s0 i < 3 := digit_lt _ _
    have hw3 : digit s1 i < 3 := digit_lt _ _
    have hdig : ∀ (c : Color) (r : ℕ), colourOfDigit (digit r j) = c → digit r j = fdigitOf c := by
      intro c r h; rw [← h, fdigitOf_colourOfDigit (digit_lt _ _)]
    have mk : ∀ v w u x : ℕ, digit s0 i = v → digit s1 i = w → digit s0 j = u → digit s1 j = x →
        slotTrace rest j = slotTrace rest i →
        (j < 3 ^ S ∧ digit s0 j = u ∧ digit s1 j = x) ∧
          M.testBit (setDigit s0 v (setDigit s1 w j)) = true := by
      intro v w u x hv hw h1 h2 h3
      refine ⟨⟨hj, h1, h2⟩, ?_⟩
      have heq : setDigit s0 v (setDigit s1 w j) = i := by
        refine hgood.inj (hsrclt _ _ (hv ▸ hv3) (hw ▸ hw3)) hi3 ?_
        rw [hsrc _ _ (hv ▸ hv3) (hw ▸ hw3), slotTrace_cons, slotTrace_cons, h3, hv, hw]
      rw [heq]; exact hbi
    rw [slotTrace_cons, slotTrace_cons, enum1_H_cons] at hmem
    by_cases hcc : colourOfDigit (digit s0 i) = colourOfDigit (digit s1 i)
    · rw [ite_eq_left hcc] at hmem
      have hvw : digit s0 i = digit s1 i := colourOfDigit_inj hv3 hw3 hcc
      simp only [slotTrace_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.cons.injEq] at hmem
      rcases hmem with ⟨ha, hbb, hT⟩ | ⟨ha, hbb, hT⟩ <;>
        rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega)
          with hv | hv | hv <;>
        rw [hv] at ha hbb
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inl ((mk 0 0 1 1 hv (hvw.symm.trans hv) (hdig _ _ ha) (hdig _ _ hbb) hT))))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 1
          1 2 2 hv (hvw.symm.trans hv) (hdig _ _ ha) (hdig _ _ hbb) hT))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 2 2 0 0 hv
          (hvw.symm.trans hv) (hdig _ _ ha) (hdig _ _ hbb) hT))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inr (mk 0 0 2 2 hv (hvw.symm.trans hv) (hdig _ _ ha) (hdig _ _ hbb) hT)))))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 1 1 0 0 hv
          (hvw.symm.trans hv) (hdig _ _ ha) (hdig _ _ hbb) hT)))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 2 2 1 1 hv (hvw.symm.trans
          hv) (hdig _ _ ha) (hdig _ _ hbb) hT)))))))
    · rw [ite_eq_right hcc] at hmem
      simp only [slotTrace_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.cons.injEq] at hmem
      obtain ⟨ha, hbb, hT⟩ := hmem
      have ha' : digit s0 j = digit s1 i := colourOfDigit_inj (digit_lt _ _) hw3 ha
      have hbb' : digit s1 j = digit s0 i := colourOfDigit_inj (digit_lt _ _) hv3 hbb
      rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega) with hv | hv | hv <;>
        rcases (show digit s1 i = 0 ∨ digit s1 i = 1 ∨ digit s1 i = 2 by omega)
          with hw | hw | hw
      · exact absurd (by rw [hv, hw]) hcc
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 0 1 1 0 hv hw (ha'.trans hw)
          (hbb'.trans hv) hT))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (mk 0 2 2 0 hv hw (ha'.trans hw) (hbb'.trans hv) hT))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 1 0 0 1 hv hw (ha'.trans hw) (hbb'.trans
          hv) hT)))))
      · exact absurd (by rw [hv, hw]) hcc
      · exact Or.inl (Or.inr (mk 1 2 2 1 hv hw (ha'.trans hw) (hbb'.trans hv) hT))
      · exact Or.inl (Or.inl (Or.inr (mk 2 0 0 2 hv hw (ha'.trans hw) (hbb'.trans hv) hT)))
      · exact Or.inr (mk 2 1 1 2 hv hw (ha'.trans hw) (hbb'.trans hv) hT)
      · exact absurd (by rw [hv, hw]) hcc

/-! ### The `K` step

Two different head colours are replaced by their sum in the head slot, and the
second slot is emptied so that it can be recycled. -/

/-- The `K` step: `(v, w) ↦ (v + w, 0)` for `v ≠ w`. -/
def stepK (S s0 s1 M : ℕ) : ℕ :=
  move2 S s0 s1 0 1 2 0 M ||| move2 S s0 s1 1 0 2 0 M
    ||| move2 S s0 s1 0 2 1 0 M ||| move2 S s0 s1 2 0 1 0 M
    ||| move2 S s0 s1 1 2 0 0 M ||| move2 S s0 s1 2 1 0 0 M

theorem stepK_spec0 {M s0 s1 S : ℕ} {rest : List ℕ} (hgood : Good M (s0 :: s1 :: rest) S)
    (j : ℕ) (hj : j < 3 ^ S) (hj1 : digit s1 j = 0) :
    ((stepK S s0 s1 M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: rest) j ∈ enum1 .K (slotTrace (s0 :: s1 :: rest) i)) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hnd := hgood.nodup
  have hne : s0 ≠ s1 := fun h =>
    (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hs0r : s0 ∉ rest := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h)
  have hs1r : s1 ∉ rest := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 h
  have hsrc : ∀ v w : ℕ, v < 3 → w < 3 →
      slotTrace (s0 :: s1 :: rest) (setDigit s0 v (setDigit s1 w j))
        = colourOfDigit v :: colourOfDigit w :: slotTrace rest j := by
    intro v w hv hw
    rw [slotTrace_cons, slotTrace_cons, digit_setDigit_self hv,
      digit_setDigit_of_ne (Ne.symm hne) hv, digit_setDigit_self hw,
      slotTrace_setDigit_of_not_mem hs0r hv, slotTrace_setDigit_of_not_mem hs1r hw]
  have hsrclt : ∀ v w : ℕ, v < 3 → w < 3 → setDigit s0 v (setDigit s1 w j) < 3 ^ S :=
    fun v w hv hw => setDigit_lt hs0 hv (setDigit_lt hs1 hw hj)
  have key : ∀ v w u : ℕ, v < 3 → w < 3 → digit s0 j = u →
      (colourOfDigit u :: slotTrace rest j) ∈
        enum1 .K (colourOfDigit v :: colourOfDigit w :: slotTrace rest j) →
      M.testBit (setDigit s0 v (setDigit s1 w j)) = true →
      ∃ i, M.testBit i = true ∧
        slotTrace (s0 :: rest) j ∈ enum1 .K (slotTrace (s0 :: s1 :: rest) i) :=
    fun v w u hv hw h1 hmem hb =>
      ⟨_, hb, by rw [hsrc v w hv hw, slotTrace_cons, h1]; exact hmem⟩
  unfold stepK
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2]
  constructor
  · rintro (((((⟨⟨-, h1, h2⟩, hb⟩ | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩) |
      ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩)
    · exact key 0 1 2 e0 e1 h1 List.mem_cons_self hb
    · exact key 1 0 2 e1 e0 h1 List.mem_cons_self hb
    · exact key 0 2 1 e0 e2 h1 List.mem_cons_self hb
    · exact key 2 0 1 e2 e0 h1 List.mem_cons_self hb
    · exact key 1 2 0 e1 e2 h1 List.mem_cons_self hb
    · exact key 2 1 0 e2 e1 h1 List.mem_cons_self hb
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    have hv3 : digit s0 i < 3 := digit_lt _ _
    have hw3 : digit s1 i < 3 := digit_lt _ _
    have hdig : ∀ (c : Color) (r : ℕ), colourOfDigit (digit r j) = c → digit r j = fdigitOf c := by
      intro c r h; rw [← h, fdigitOf_colourOfDigit (digit_lt _ _)]
    have mk : ∀ v w u : ℕ, digit s0 i = v → digit s1 i = w → digit s0 j = u →
        slotTrace rest j = slotTrace rest i →
        (j < 3 ^ S ∧ digit s0 j = u ∧ digit s1 j = 0) ∧
          M.testBit (setDigit s0 v (setDigit s1 w j)) = true := by
      intro v w u hv hw h1 h3
      refine ⟨⟨hj, h1, hj1⟩, ?_⟩
      have heq : setDigit s0 v (setDigit s1 w j) = i := by
        refine hgood.inj (hsrclt _ _ (hv ▸ hv3) (hw ▸ hw3)) hi3 ?_
        rw [hsrc _ _ (hv ▸ hv3) (hw ▸ hw3), slotTrace_cons, slotTrace_cons, h3, hv, hw]
      rw [heq]; exact hbi
    rw [slotTrace_cons, slotTrace_cons, enum1_K_cons] at hmem
    by_cases hcc : colourOfDigit (digit s0 i) = colourOfDigit (digit s1 i)
    · rw [ite_eq_left hcc] at hmem; simp at hmem
    · rw [ite_eq_right hcc] at hmem
      simp only [slotTrace_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.cons.injEq] at hmem
      obtain ⟨ha, hT⟩ := hmem
      rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega) with hv | hv | hv <;>
        rcases (show digit s1 i = 0 ∨ digit s1 i = 1 ∨ digit s1 i = 2 by omega)
          with hw | hw | hw <;>
        rw [hv, hw] at ha
      · exact absurd (by rw [hv, hw]) hcc
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ((mk 0 1 2 hv hw (hdig _ _ ha) hT))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (mk 0 2 1 hv hw (hdig _ _ ha) hT))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mk 1 0 2 hv hw (hdig _ _ ha) hT)))))
      · exact absurd (by rw [hv, hw]) hcc
      · exact Or.inl (Or.inr (mk 1 2 0 hv hw (hdig _ _ ha) hT))
      · exact Or.inl (Or.inl (Or.inr (mk 2 0 1 hv hw (hdig _ _ ha) hT)))
      · exact Or.inr (mk 2 1 0 hv hw (hdig _ _ ha) hT)
      · exact absurd (by rw [hv, hw]) hcc

/-! ### The `A` step

Two equal head colours are deleted, emptying both their slots.  When they are
the whole ring the traces with equal head colours are kept instead. -/

/-- The `A` step: `(v, v) ↦ (0, 0)`, both slots freed. -/
def stepA (S s0 s1 M : ℕ) : ℕ :=
  move2 S s0 s1 0 0 0 0 M ||| move2 S s0 s1 1 1 0 0 M ||| move2 S s0 s1 2 2 0 0 M

/-- The `A` step on a ring of length two: the traces with equal colours are kept. -/
def stepA2 (S s0 s1 M : ℕ) : ℕ :=
  move2 S s0 s1 0 0 0 0 M ||| move2 S s0 s1 1 1 1 1 M ||| move2 S s0 s1 2 2 2 2 M

theorem enum1_A_cons' (e₁ e₂ c : Color) (et : List Color) :
    enum1 .A (e₁ :: e₂ :: c :: et) = if e₁ = e₂ then [c :: et] else [] := rfl

theorem enum1_A_pair (e₁ e₂ : Color) :
    enum1 .A [e₁, e₂] = if e₁ = e₂ then [[e₁, e₂]] else [] := rfl

theorem stepA_spec0 {M s0 s1 S r : ℕ} {rs : List ℕ}
    (hgood : Good M (s0 :: s1 :: r :: rs) S) (j : ℕ) (hj : j < 3 ^ S)
    (hj0 : digit s0 j = 0) (hj1 : digit s1 j = 0) :
    ((stepA S s0 s1 M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧
        slotTrace (r :: rs) j ∈ enum1 .A (slotTrace (s0 :: s1 :: r :: rs) i)) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hnd := hgood.nodup
  have hne : s0 ≠ s1 := fun h =>
    (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hs0r : s0 ∉ r :: rs := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h)
  have hs1r : s1 ∉ r :: rs := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 h
  have hsrc : ∀ v w : ℕ, v < 3 → w < 3 →
      slotTrace (s0 :: s1 :: r :: rs) (setDigit s0 v (setDigit s1 w j))
        = colourOfDigit v :: colourOfDigit w :: slotTrace (r :: rs) j := by
    intro v w hv hw
    rw [slotTrace_cons, slotTrace_cons, digit_setDigit_self hv,
      digit_setDigit_of_ne (Ne.symm hne) hv, digit_setDigit_self hw,
      slotTrace_setDigit_of_not_mem hs0r hv, slotTrace_setDigit_of_not_mem hs1r hw]
  have hsrclt : ∀ v w : ℕ, v < 3 → w < 3 → setDigit s0 v (setDigit s1 w j) < 3 ^ S :=
    fun v w hv hw => setDigit_lt hs0 hv (setDigit_lt hs1 hw hj)
  have key : ∀ v : ℕ, v < 3 →
      (slotTrace (r :: rs) j) ∈
        enum1 .A (colourOfDigit v :: colourOfDigit v :: slotTrace (r :: rs) j) →
      M.testBit (setDigit s0 v (setDigit s1 v j)) = true →
      ∃ i, M.testBit i = true ∧
        slotTrace (r :: rs) j ∈ enum1 .A (slotTrace (s0 :: s1 :: r :: rs) i) :=
    fun v hv hmem hb => ⟨_, hb, by rw [hsrc v v hv hv]; exact hmem⟩
  unfold stepA
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2]
  constructor
  · rintro ((⟨⟨-, h1, h2⟩, hb⟩ | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩)
    · exact key 0 e0 List.mem_cons_self hb
    · exact key 1 e1 List.mem_cons_self hb
    · exact key 2 e2 List.mem_cons_self hb
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    have hv3 : digit s0 i < 3 := digit_lt _ _
    have hw3 : digit s1 i < 3 := digit_lt _ _
    have mk : ∀ v : ℕ, digit s0 i = v → digit s1 i = v →
        slotTrace (r :: rs) j = slotTrace (r :: rs) i →
        (j < 3 ^ S ∧ digit s0 j = 0 ∧ digit s1 j = 0) ∧
          M.testBit (setDigit s0 v (setDigit s1 v j)) = true := by
      intro v hv hw h3
      refine ⟨⟨hj, hj0, hj1⟩, ?_⟩
      have heq : setDigit s0 v (setDigit s1 v j) = i := by
        refine hgood.inj (hsrclt _ _ (hv ▸ hv3) (hw ▸ hw3)) hi3 ?_
        rw [hsrc _ _ (hv ▸ hv3) (hw ▸ hw3), h3]
        conv_rhs => rw [slotTrace_cons, slotTrace_cons]
        rw [hv, hw]
      rw [heq]; exact hbi
    simp only [slotTrace_cons] at hmem
    rw [enum1_A_cons'] at hmem
    by_cases hcc : colourOfDigit (digit s0 i) = colourOfDigit (digit s1 i)
    · rw [ite_eq_left hcc] at hmem
      have hvw : digit s0 i = digit s1 i := colourOfDigit_inj hv3 hw3 hcc
      simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at hmem
      have hT : slotTrace (r :: rs) j = slotTrace (r :: rs) i := by
        rw [slotTrace_cons, slotTrace_cons, hmem.1, hmem.2]
      rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega) with hv | hv | hv
      · exact Or.inl (Or.inl ((mk 0 hv (hvw.symm.trans hv) hT)))
      · exact Or.inl (Or.inr (mk 1 hv (hvw.symm.trans hv) hT))
      · exact Or.inr (mk 2 hv (hvw.symm.trans hv) hT)
    · rw [ite_eq_right hcc] at hmem; simp at hmem

theorem stepA2_spec {M s0 s1 S : ℕ} (hgood : Good M [s0, s1] S) (j : ℕ) (hj : j < 3 ^ S) :
    ((stepA2 S s0 s1 M).testBit j = true ↔
      ∃ i, M.testBit i = true ∧ slotTrace [s0, s1] j ∈ enum1 .A (slotTrace [s0, s1] i)) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hne : s0 ≠ s1 := fun h =>
    (List.nodup_cons.mp hgood.nodup).1 (by rw [h]; exact List.mem_cons_self)
  have hsrc : ∀ v w : ℕ, v < 3 → w < 3 →
      slotTrace [s0, s1] (setDigit s0 v (setDigit s1 w j))
        = [colourOfDigit v, colourOfDigit w] := by
    intro v w hv hw
    rw [slotTrace_cons, slotTrace_cons, slotTrace_nil, digit_setDigit_self hv,
      digit_setDigit_of_ne (Ne.symm hne) hv, digit_setDigit_self hw]
  have hsrclt : ∀ v w : ℕ, v < 3 → w < 3 → setDigit s0 v (setDigit s1 w j) < 3 ^ S :=
    fun v w hv hw => setDigit_lt hs0 hv (setDigit_lt hs1 hw hj)
  have key : ∀ v u x : ℕ, v < 3 → digit s0 j = u → digit s1 j = x →
      [colourOfDigit u, colourOfDigit x] ∈ enum1 .A [colourOfDigit v, colourOfDigit v] →
      M.testBit (setDigit s0 v (setDigit s1 v j)) = true →
      ∃ i, M.testBit i = true ∧ slotTrace [s0, s1] j ∈ enum1 .A (slotTrace [s0, s1] i) :=
    fun v u x hv h1 h2 hmem hb =>
      ⟨_, hb, by
        rw [hsrc v v hv hv, slotTrace_cons, slotTrace_cons, slotTrace_nil, h1, h2]
        exact hmem⟩
  unfold stepA2
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2]
  constructor
  · rintro ((⟨⟨-, h1, h2⟩, hb⟩ | ⟨⟨-, h1, h2⟩, hb⟩) | ⟨⟨-, h1, h2⟩, hb⟩)
    · exact key 0 0 0 e0 h1 h2 List.mem_cons_self hb
    · exact key 1 1 1 e1 h1 h2 List.mem_cons_self hb
    · exact key 2 2 2 e2 h1 h2 List.mem_cons_self hb
  · rintro ⟨i, hbi, hmem⟩
    have hi3 := hgood.bit_lt i hbi
    have hv3 : digit s0 i < 3 := digit_lt _ _
    have hw3 : digit s1 i < 3 := digit_lt _ _
    have mk : ∀ v u x : ℕ, digit s0 i = v → digit s1 i = v → digit s0 j = u → digit s1 j = x →
        (j < 3 ^ S ∧ digit s0 j = u ∧ digit s1 j = x) ∧
          M.testBit (setDigit s0 v (setDigit s1 v j)) = true := by
      intro v u x hv hw h1 h2
      refine ⟨⟨hj, h1, h2⟩, ?_⟩
      have heq : setDigit s0 v (setDigit s1 v j) = i := by
        refine hgood.inj (hsrclt _ _ (hv ▸ hv3) (hw ▸ hw3)) hi3 ?_
        rw [hsrc _ _ (hv ▸ hv3) (hw ▸ hw3)]
        conv_rhs => rw [slotTrace_cons, slotTrace_cons, slotTrace_nil]
        rw [hv, hw]
      rw [heq]; exact hbi
    simp only [slotTrace_cons, slotTrace_nil] at hmem
    rw [enum1_A_pair] at hmem
    by_cases hcc : colourOfDigit (digit s0 i) = colourOfDigit (digit s1 i)
    · rw [ite_eq_left hcc] at hmem
      have hvw : digit s0 i = digit s1 i := colourOfDigit_inj hv3 hw3 hcc
      simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at hmem
      have ha' : digit s0 j = digit s0 i :=
        colourOfDigit_inj (digit_lt _ _) hv3 hmem.1
      have hbb' : digit s1 j = digit s1 i :=
        colourOfDigit_inj (digit_lt _ _) hw3 hmem.2.1
      rcases (show digit s0 i = 0 ∨ digit s0 i = 1 ∨ digit s0 i = 2 by omega) with hv | hv | hv
      · exact Or.inl (Or.inl ((mk 0 0 0 hv (hvw.symm.trans hv) (ha'.trans hv) (hbb'.trans
          (hvw.symm.trans hv)))))
      · exact Or.inl (Or.inr (mk 1 1 1 hv (hvw.symm.trans hv) (ha'.trans hv) (hbb'.trans
          (hvw.symm.trans hv))))
      · exact Or.inr (mk 2 2 2 hv (hvw.symm.trans hv) (ha'.trans hv) (hbb'.trans (hvw.symm.trans
          hv)))
    · rw [ite_eq_right hcc] at hmem; simp at hmem

/-! ### Recycling a freed slot

After a `K` or an `A` step the slots of the deleted ring positions hold `0` in
every live index.  Exchanging such a slot with the top slot `S - 1` frees the
top slot, and the mask then lives below `3 ^ (S - 1)`: the number of slots
never exceeds the ring size. -/

theorem tau_injective (s t : ℕ) : Function.Injective (tau s t) := by
  intro a b h
  have := congrArg (tau s t) h
  rwa [tau_tau, tau_tau] at this

theorem swapIdx_self (s j : ℕ) : swapIdx s s j = j := by
  rw [swapIdx, setDigit_setDigit _ _ _ _ (digit_lt s j) (digit_lt s j), setDigit_digit_self]

/-- The mask of the exchange of the freed slot `d` with the top slot `S - 1`. -/
def recycleMask (d S M : ℕ) : ℕ := if d = S - 1 then M else swap0 S d (S - 1) M

/-- Exchange the freed slot `d` with the top slot, and drop the top slot. -/
def recycle (d : ℕ) (st : ℕ × List ℕ × ℕ) : ℕ × List ℕ × ℕ :=
  (recycleMask d st.2.2 st.1, st.2.1.map (tau d (st.2.2 - 1)), st.2.2 - 1)

theorem recycle_eq (d M S : ℕ) (order : List ℕ) :
    recycle d (M, order, S) = (recycleMask d S M, order.map (tau d (S - 1)), S - 1) := rfl

theorem testBit_recycleMask {M S d : ℕ} (hd : d < S) (hS : 1 ≤ S) (j : ℕ)
    (hj : j < 3 ^ (S - 1)) :
    (recycleMask d S M).testBit j = M.testBit (swapIdx d (S - 1) j) := by
  have hjS : j < 3 ^ S := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have htop : digit (S - 1) j = 0 := digit_eq_zero_of_lt hj (le_refl _)
  unfold recycleMask
  split_ifs with hdt
  · rw [hdt, swapIdx_self]
  · rw [testBit_swap0 hd (by omega) hdt]
    simp [hjS, htop]

theorem recycleMask_bit {M S d : ℕ} (hd : d < S) (hS : 1 ≤ S)
    (hbit : ∀ i, M.testBit i = true → i < 3 ^ S ∧ digit d i = 0) (j : ℕ)
    (h : (recycleMask d S M).testBit j = true) :
    j < 3 ^ (S - 1) ∧ M.testBit (swapIdx d (S - 1) j) = true := by
  have hSS : S - 1 + 1 = S := by omega
  unfold recycleMask at h
  split_ifs at h with hdt
  · have hb := hbit j h
    refine ⟨lt_of_digit_zero (k := S - 1) (by rw [hSS]; exact hb.1)
      (by rw [← hdt]; exact hb.2), ?_⟩
    rw [hdt, swapIdx_self]; exact h
  · rw [testBit_swap0 hd (by omega) hdt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨lt_of_digit_zero (k := S - 1) (by rw [hSS]; exact h.1.1) h.1.2, h.2⟩

theorem slotTrace_map_tau (d S : ℕ) (order : List ℕ) (j : ℕ) :
    slotTrace (order.map (tau d (S - 1))) j = slotTrace order (swapIdx d (S - 1) j) :=
  (slotTrace_swapIdx d (S - 1) order j).symm

theorem tau_lt_of_mem {order : List ℕ} {S d r : ℕ} (hlt : ∀ s ∈ order, s < S) (hdm : d ∉ order)
    (hd : d < S) (hr : r ∈ order) : tau d (S - 1) r < S - 1 := by
  have hrS : r < S := hlt r hr
  have hrd : r ≠ d := fun h => hdm (h ▸ hr)
  unfold tau
  split_ifs with h1 h2 <;> omega

theorem recycle_good {M : ℕ} {order : List ℕ} {S d : ℕ} (hnd : order.Nodup)
    (hlt : ∀ s ∈ order, s < S) (hlen : order.length = S - 1) (hdm : d ∉ order) (hd : d < S)
    (hS : 2 ≤ S) (hbit : ∀ i, M.testBit i = true → i < 3 ^ S ∧ digit d i = 0) :
    Good (recycleMask d S M) (order.map (tau d (S - 1))) (S - 1) where
  nodup := hnd.map (tau_injective _ _)
  slot_lt := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact tau_lt_of_mem hlt hdm hd hr
  len := by rw [List.length_map, hlen]
  pos := by omega
  bit_lt := fun i hi => (recycleMask_bit hd (by omega) hbit i hi).1

/-! ### The index bounds of the step masks -/

theorem stepY_bit_lt {S s0 : ℕ} (hs0 : s0 < S) (M j : ℕ)
    (h : (stepY S s0 M).testBit j = true) : j < 3 ^ (S + 1) := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  rw [stepY] at h
  simp only [Nat.testBit_or, Bool.or_eq_true,
    testBit_move2_iff (show s0 < S + 1 by omega) (show S < S + 1 by omega)
      (show s0 ≠ S by omega), e0, e1, e2] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  all_goals exact h.1.1

theorem stepH_bit_lt {S s0 s1 : ℕ} (hs0 : s0 < S) (hs1 : s1 < S) (hne : s0 ≠ s1) (M j : ℕ)
    (h : (stepH S s0 s1 M).testBit j = true) : j < 3 ^ S := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  rw [stepH] at h
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2] at h
  rcases h with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  all_goals exact h.1.1

theorem stepK_bit {S s0 s1 : ℕ} (hs0 : s0 < S) (hs1 : s1 < S) (hne : s0 ≠ s1) (M j : ℕ)
    (h : (stepK S s0 s1 M).testBit j = true) : j < 3 ^ S ∧ digit s1 j = 0 := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  rw [stepK] at h
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  all_goals exact ⟨h.1.1, h.1.2.2⟩

theorem stepA_bit {S s0 s1 : ℕ} (hs0 : s0 < S) (hs1 : s1 < S) (hne : s0 ≠ s1) (M j : ℕ)
    (h : (stepA S s0 s1 M).testBit j = true) :
    j < 3 ^ S ∧ digit s0 j = 0 ∧ digit s1 j = 0 := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  rw [stepA] at h
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2] at h
  rcases h with ((h | h) | h)
  all_goals exact ⟨h.1.1, h.1.2.1, h.1.2.2⟩

theorem stepA2_bit_lt {S s0 s1 : ℕ} (hs0 : s0 < S) (hs1 : s1 < S) (hne : s0 ≠ s1) (M j : ℕ)
    (h : (stepA2 S s0 s1 M).testBit j = true) : j < 3 ^ S := by
  have e0 : (0 : ℕ) < 3 := by norm_num
  have e1 : (1 : ℕ) < 3 := by norm_num
  have e2 : (2 : ℕ) < 3 := by norm_num
  rw [stepA2] at h
  simp only [Nat.testBit_or, Bool.or_eq_true, testBit_move2_iff hs0 hs1 hne, e0, e1, e2] at h
  rcases h with ((h | h) | h)
  all_goals exact h.1.1

/-! ### The `K` and `A` steps with their slots recycled -/

theorem bulkStepK_spec {M s0 s1 S : ℕ} {rest : List ℕ} (hgood : Good M (s0 :: s1 :: rest) S) :
    Good (recycleMask s1 S (stepK S s0 s1 M)) ((s0 :: rest).map (tau s1 (S - 1))) (S - 1) ∧
    ∀ j, j < 3 ^ (S - 1) →
      ((recycleMask s1 S (stepK S s0 s1 M)).testBit j = true ↔
        ∃ i, M.testBit i = true ∧
          slotTrace ((s0 :: rest).map (tau s1 (S - 1))) j ∈
            enum1 .K (slotTrace (s0 :: s1 :: rest) i)) := by
  have hnd := hgood.nodup
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hne : s0 ≠ s1 := fun h => (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hlen : rest.length + 2 = S := by have := hgood.len; simp at this; omega
  have hS2 : 2 ≤ S := by omega
  have hnd2 : (s1 :: rest).Nodup := (List.nodup_cons.mp hnd).2
  have hs0m : s0 ∉ rest := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h)
  have hs1m : s1 ∉ rest := (List.nodup_cons.mp hnd2).1
  have hnd1 : (s0 :: rest).Nodup := List.nodup_cons.mpr ⟨hs0m, (List.nodup_cons.mp hnd2).2⟩
  have hlt1 : ∀ s ∈ s0 :: rest, s < S := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact hs0
    · exact hgood.slot_lt s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs'))
  have hs1m1 : s1 ∉ s0 :: rest := by
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact hne h'.symm
    · exact hs1m h'
  have hbit1 : ∀ i, (stepK S s0 s1 M).testBit i = true → i < 3 ^ S ∧ digit s1 i = 0 :=
    fun i h => stepK_bit hs0 hs1 hne M i h
  refine ⟨recycle_good hnd1 hlt1 (by simp; omega) hs1m1 hs1 hS2 hbit1, fun j hj => ?_⟩
  have hjS : swapIdx s1 (S - 1) j < 3 ^ S :=
    swapIdx_lt hs1 (by omega) (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hdig : digit s1 (swapIdx s1 (S - 1) j) = 0 := by
    rw [digit_swapIdx, tau_left]
    exact digit_eq_zero_of_lt hj (le_refl _)
  rw [testBit_recycleMask hs1 (by omega) j hj, slotTrace_map_tau]
  exact stepK_spec0 hgood _ hjS hdig

theorem bulkStepA_spec {M s0 s1 S r : ℕ} {rs : List ℕ}
    (hgood : Good M (s0 :: s1 :: r :: rs) S) :
    Good (recycleMask (tau s1 (S - 1) s0) (S - 1) (recycleMask s1 S (stepA S s0 s1 M)))
      (((r :: rs).map (tau s1 (S - 1))).map (tau (tau s1 (S - 1) s0) (S - 1 - 1)))
      (S - 1 - 1) ∧
    ∀ j, j < 3 ^ (S - 1 - 1) →
      ((recycleMask (tau s1 (S - 1) s0) (S - 1)
          (recycleMask s1 S (stepA S s0 s1 M))).testBit j = true ↔
        ∃ i, M.testBit i = true ∧
          slotTrace (((r :: rs).map (tau s1 (S - 1))).map (tau (tau s1 (S - 1) s0) (S - 1 - 1))) j
            ∈ enum1 .A (slotTrace (s0 :: s1 :: r :: rs) i)) := by
  have hnd := hgood.nodup
  have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
  have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
  have hne : s0 ≠ s1 := fun h => (List.nodup_cons.mp hnd).1 (by rw [h]; exact List.mem_cons_self)
  have hlen : rs.length + 3 = S := by have := hgood.len; simp at this; omega
  have hS3 : 3 ≤ S := by omega
  have hnd2 : (s1 :: r :: rs).Nodup := (List.nodup_cons.mp hnd).2
  have hs0m : s0 ∉ r :: rs := fun h => (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ h)
  have hs1m : s1 ∉ r :: rs := (List.nodup_cons.mp hnd2).1
  have hndr : (r :: rs).Nodup := (List.nodup_cons.mp hnd2).2
  have hltr : ∀ s ∈ r :: rs, s < S := fun s hs =>
    hgood.slot_lt s (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs))
  have hbit1 : ∀ i, (stepA S s0 s1 M).testBit i = true →
      i < 3 ^ S ∧ digit s0 i = 0 ∧ digit s1 i = 0 := fun i h => stepA_bit hs0 hs1 hne M i h
  have hs1m1 : s1 ∉ s0 :: r :: rs := by
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact hne h'.symm
    · exact hs1m h'
  have hlt01 : ∀ s ∈ s0 :: r :: rs, s < S := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact hs0
    · exact hltr s hs'
  have hd0lt : tau s1 (S - 1) s0 < S - 1 :=
    tau_lt_of_mem hlt01 hs1m1 hs1 List.mem_cons_self
  have hbit2 : ∀ i, (recycleMask s1 S (stepA S s0 s1 M)).testBit i = true →
      i < 3 ^ (S - 1) ∧ digit (tau s1 (S - 1) s0) i = 0 := by
    intro i hi
    have h := recycleMask_bit hs1 (by omega)
      (fun k hk => ⟨(hbit1 k hk).1, (hbit1 k hk).2.2⟩) i hi
    refine ⟨h.1, ?_⟩
    have h2 := (hbit1 _ h.2).2.1
    rwa [digit_swapIdx] at h2
  have hndm : ((r :: rs).map (tau s1 (S - 1))).Nodup := hndr.map (tau_injective _ _)
  have hltm : ∀ s ∈ (r :: rs).map (tau s1 (S - 1)), s < S - 1 := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    exact tau_lt_of_mem hltr hs1m hs1 hx
  have hd0m : tau s1 (S - 1) s0 ∉ (r :: rs).map (tau s1 (S - 1)) := by
    intro h
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
    exact hs0m (by rwa [tau_injective _ _ hxe] at hx)
  refine ⟨recycle_good hndm hltm (by simp; omega) hd0m hd0lt (by omega) hbit2, fun j hj => ?_⟩
  have hj1 : swapIdx (tau s1 (S - 1) s0) (S - 1 - 1) j < 3 ^ (S - 1) :=
    swapIdx_lt hd0lt (by omega)
      (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hj2 : swapIdx s1 (S - 1) (swapIdx (tau s1 (S - 1) s0) (S - 1 - 1) j) < 3 ^ S :=
    swapIdx_lt hs1 (by omega) (lt_of_lt_of_le hj1 (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hdig1 : digit s1 (swapIdx s1 (S - 1) (swapIdx (tau s1 (S - 1) s0) (S - 1 - 1) j)) = 0 := by
    rw [digit_swapIdx, tau_left]
    exact digit_eq_zero_of_lt hj1 (le_refl _)
  have hdig0 : digit s0 (swapIdx s1 (S - 1) (swapIdx (tau s1 (S - 1) s0) (S - 1 - 1) j)) = 0 := by
    rw [digit_swapIdx, digit_swapIdx, tau_left]
    exact digit_eq_zero_of_lt hj (le_refl _)
  rw [testBit_recycleMask hd0lt (by omega) j hj, slotTrace_map_tau,
    testBit_recycleMask hs1 (by omega) _ hj1, slotTrace_map_tau]
  exact stepA_spec0 hgood _ hj2 hdig0 hdig1

/-! ### One bulk step

`bulkStep` mirrors `enum1`: `R`/`R'` rotate the slot list, `U` and `Y` allocate
fresh slots, `H` rewrites in place, and `K`/`A` delete ring positions and
recycle the slots they free. -/

theorem enum1_R'_of_two_le {t : List Color} (h : 2 ≤ t.length) :
    enum1 .R' t = [t.rotate (t.length - 1)] := by
  rw [enum1_R', ite_eq_right (by omega)]

/-- The ring length after one step, matching `cprsize`. -/
def stepLen : CpStep → ℕ → ℕ
  | .R _, n => n
  | .R', n => n
  | .Y, n => n + 1
  | .H, n => n
  | .U, n => n + 2
  | .K, n => n - 2 + 1
  | .A, n => sub2ifgt2 n

/-- One construction step on a bulk state. -/
def bulkStep (s : CpStep) (st : ℕ × List ℕ × ℕ) : ℕ × List ℕ × ℕ :=
  match s, st with
  | .R n, (M, order, S) => (M, order.rotate n, S)
  | .R', (M, order, S) =>
      match order with
      | [] => (0, [], S)
      | [s0] => (0, [s0], S)
      | s0 :: s1 :: rest =>
          (M, (s0 :: s1 :: rest).rotate ((s0 :: s1 :: rest).length - 1), S)
  | .U, (M, order, S) => (stepU S M, S :: (S + 1) :: order, S + 2)
  | .Y, (M, order, S) =>
      match order with
      | [] => (0, [], S)
      | s0 :: rest => (stepY S s0 M, s0 :: S :: rest, S + 1)
  | .H, (M, order, S) =>
      match order with
      | s0 :: s1 :: rest => (stepH S s0 s1 M, s0 :: s1 :: rest, S)
      | o => (0, o, S)
  | .K, (M, order, S) =>
      match order with
      | s0 :: s1 :: rest => recycle s1 (stepK S s0 s1 M, s0 :: rest, S)
      | o => (0, o, S)
  | .A, (M, order, S) =>
      match order with
      | s0 :: s1 :: rest =>
          match rest with
          | [] => (stepA2 S s0 s1 M, [s0, s1], S)
          | r :: rs => recycle (tau s1 (S - 1) s0) (recycle s1 (stepA S s0 s1 M, r :: rs, S))
      | o => (0, o, S)

/-- What one bulk step achieves: the new state is good, its ring length is the
one `cprsize` predicts, and its bits are exactly the traces `enum1` enumerates
from the traces of the old bits. -/
def StepOK (s : CpStep) (M : ℕ) (order : List ℕ) (S : ℕ)
    (M' : ℕ) (order' : List ℕ) (S' : ℕ) : Prop :=
  Good M' order' S' ∧ S' = stepLen s S ∧
    ∀ j, j < 3 ^ S' → (M'.testBit j = true ↔
      ∃ i, M.testBit i = true ∧ slotTrace order' j ∈ enum1 s (slotTrace order i))

/-- A step that enumerates nothing produces the empty mask. -/
theorem stepOK_zero {M : ℕ} {order : List ℕ} {S : ℕ} {s : CpStep} (hgood : Good M order S)
    (hS : S = stepLen s S) (hnil : ∀ i : ℕ, enum1 s (slotTrace order i) = []) :
    StepOK s M order S 0 order S := by
  refine ⟨⟨hgood.nodup, hgood.slot_lt, hgood.len, hgood.pos, by simp⟩, hS,
    fun j _ => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨i, -, hmem⟩
  rw [hnil i] at hmem
  simp at hmem

theorem bulkStep_spec (s : CpStep) {M : ℕ} {order : List ℕ} {S : ℕ} (hgood : Good M order S) :
    StepOK s M order S (bulkStep s (M, order, S)).1 (bulkStep s (M, order, S)).2.1
      (bulkStep s (M, order, S)).2.2 := by
  cases s with
  | R n =>
    change StepOK (.R n) M order S M (order.rotate n) S
    refine ⟨⟨List.nodup_rotate.mpr hgood.nodup,
      fun x hx => hgood.slot_lt x (List.mem_rotate.mp hx),
      by rw [List.length_rotate]; exact hgood.len, hgood.pos, hgood.bit_lt⟩, rfl, fun j hj => ?_⟩
    simp only [enum1_R, List.mem_singleton, slotTrace_rotate]
    constructor
    · intro h; exact ⟨j, h, rfl⟩
    · rintro ⟨i, hbi, he⟩
      have hji : j = i := hgood.inj hj (hgood.bit_lt i hbi) (List.rotate_injective n he)
      rw [hji]; exact hbi
  | R' =>
    match order, hgood with
    | [], hgood => exact stepOK_zero hgood rfl (fun _ => rfl)
    | [s0], hgood => exact stepOK_zero hgood rfl (fun _ => rfl)
    | s0 :: s1 :: rest, hgood =>
      change StepOK .R' M (s0 :: s1 :: rest) S M
        ((s0 :: s1 :: rest).rotate ((s0 :: s1 :: rest).length - 1)) S
      have h2 : ∀ i : ℕ, 2 ≤ (slotTrace (s0 :: s1 :: rest) i).length := by
        intro i; rw [length_slotTrace]; simp
      refine ⟨⟨List.nodup_rotate.mpr hgood.nodup,
        fun x hx => hgood.slot_lt x (List.mem_rotate.mp hx),
        by rw [List.length_rotate]; exact hgood.len, hgood.pos, hgood.bit_lt⟩, rfl,
        fun j hj => ?_⟩
      constructor
      · intro h
        refine ⟨j, h, ?_⟩
        rw [slotTrace_rotate, enum1_R'_of_two_le (h2 j), length_slotTrace]
        exact List.mem_singleton_self _
      · rintro ⟨i, hbi, hmem⟩
        rw [slotTrace_rotate, enum1_R'_of_two_le (h2 i), length_slotTrace,
          List.mem_singleton] at hmem
        have hji : j = i :=
          hgood.inj hj (hgood.bit_lt i hbi) (List.rotate_injective _ hmem)
        rw [hji]; exact hbi
  | U =>
    change StepOK .U M order S (stepU S M) (S :: (S + 1) :: order) (S + 2)
    have hSo : S ∉ order := fun h => absurd (hgood.slot_lt S h) (by omega)
    have hS1o : S + 1 ∉ order := fun h => absurd (hgood.slot_lt _ h) (by omega)
    refine ⟨⟨?_, ?_, ?_, by omega, fun i hi => (testBit_stepU S M i |>.mp hi).1⟩, rfl,
      fun j hj => stepU_spec hgood j hj⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hS1o, hgood.nodup⟩⟩
      intro h
      rcases List.mem_cons.mp h with h' | h'
      · omega
      · exact hSo h'
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      rcases List.mem_cons.mp hx' with rfl | hx''
      · omega
      · exact lt_trans (hgood.slot_lt x hx'') (by omega)
    · rw [List.length_cons, List.length_cons, hgood.len]
  | Y =>
    cases order with
    | nil =>
      exact absurd hgood.pos (by have := hgood.len; simp at this; omega)
    | cons s0 rest =>
      change StepOK .Y M (s0 :: rest) S (stepY S s0 M) (s0 :: S :: rest) (S + 1)
      have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
      have hs0r : s0 ∉ rest := (List.nodup_cons.mp hgood.nodup).1
      have hSr : S ∉ rest := fun h =>
        absurd (hgood.slot_lt S (List.mem_cons_of_mem _ h)) (by omega)
      refine ⟨⟨?_, ?_, ?_, by omega, fun i hi => stepY_bit_lt hs0 M i hi⟩, rfl,
        fun j hj => stepY_spec hgood j hj⟩
      · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hSr,
          (List.nodup_cons.mp hgood.nodup).2⟩⟩
        intro h
        rcases List.mem_cons.mp h with h' | h'
        · omega
        · exact hs0r h'
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        rcases List.mem_cons.mp hx' with rfl | hx''
        · omega
        · exact lt_trans (hgood.slot_lt x (List.mem_cons_of_mem _ hx'')) (by omega)
      · have := hgood.len
        simp only [List.length_cons] at this ⊢
        omega
  | H =>
    match order, hgood with
    | [], hgood => exact stepOK_zero hgood rfl (fun _ => rfl)
    | [s0], hgood => exact stepOK_zero hgood rfl (fun _ => rfl)
    | s0 :: s1 :: rest, hgood =>
      have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
      have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
      have hne : s0 ≠ s1 := fun h =>
        (List.nodup_cons.mp hgood.nodup).1 (by rw [h]; exact List.mem_cons_self)
      exact ⟨⟨hgood.nodup, hgood.slot_lt, hgood.len, hgood.pos,
        fun i hi => stepH_bit_lt hs0 hs1 hne M i hi⟩, rfl, fun j hj => stepH_spec hgood j hj⟩
  | K =>
    match order, hgood with
    | [], hgood => exact absurd hgood.pos (by have := hgood.len; simp at this; omega)
    | [s0], hgood =>
      have hS1 : S = 1 := by have := hgood.len; simp at this; omega
      exact stepOK_zero hgood (by rw [stepLen, hS1]) (fun _ => rfl)
    | s0 :: s1 :: rest, hgood =>
      change StepOK .K M (s0 :: s1 :: rest) S (recycleMask s1 S (stepK S s0 s1 M))
        ((s0 :: rest).map (tau s1 (S - 1))) (S - 1)
      have hlen : rest.length + 2 = S := by have := hgood.len; simp at this; omega
      obtain ⟨hg, hspec⟩ := bulkStepK_spec hgood
      exact ⟨hg, by rw [stepLen]; omega, hspec⟩
  | A =>
    match order, hgood with
    | [], hgood => exact absurd hgood.pos (by have := hgood.len; simp at this; omega)
    | [s0], hgood =>
      have hS1 : S = 1 := by have := hgood.len; simp at this; omega
      refine stepOK_zero hgood ?_ (fun _ => rfl)
      rw [stepLen, hS1]
      rfl
    | [s0, s1], hgood =>
      have hS2 : S = 2 := by have := hgood.len; simp at this; omega
      have hs0 : s0 < S := hgood.slot_lt s0 List.mem_cons_self
      have hs1 : s1 < S := hgood.slot_lt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
      have hne : s0 ≠ s1 := fun h =>
        (List.nodup_cons.mp hgood.nodup).1 (by rw [h]; exact List.mem_cons_self)
      refine ⟨⟨hgood.nodup, hgood.slot_lt, hgood.len, hgood.pos,
        fun i hi => stepA2_bit_lt hs0 hs1 hne M i hi⟩, ?_, fun j hj => stepA2_spec hgood j hj⟩
      rw [stepLen, hS2]
      rfl
    | s0 :: s1 :: r :: rs, hgood =>
      change StepOK .A M (s0 :: s1 :: r :: rs) S
        (recycleMask (tau s1 (S - 1) s0) (S - 1) (recycleMask s1 S (stepA S s0 s1 M)))
        (((r :: rs).map (tau s1 (S - 1))).map (tau (tau s1 (S - 1) s0) (S - 1 - 1)))
        (S - 1 - 1)
      have hlen : rs.length + 3 = S := by have := hgood.len; simp at this; omega
      obtain ⟨hg, hspec⟩ := bulkStepA_spec hgood
      refine ⟨hg, ?_, hspec⟩
      rw [stepLen]
      unfold sub2ifgt2
      rw [ite_eq_left (show 2 < S by omega)]
      omega

/-! ### Lengths and the whole fold -/

theorem length_enum1 (s : CpStep) (t : List Color) :
    ∀ u ∈ enum1 s t, u.length = stepLen s t.length := by
  cases s with
  | R n => intro u hu; simp only [enum1_R, List.mem_singleton] at hu; subst hu; simp [stepLen]
  | R' =>
    intro u hu
    rw [enum1_R'] at hu
    split at hu
    · simp at hu
    · simp only [List.mem_singleton] at hu
      subst hu; simp [stepLen]
  | U =>
    intro u hu
    simp only [enum1_U, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> simp [stepLen]
  | Y =>
    cases t with
    | nil => simp
    | cons e₁ t' =>
      intro u hu
      simp only [enum1_Y_cons, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> simp [stepLen]
  | K =>
    match t with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: t' =>
      intro u hu
      rw [enum1_K_cons] at hu
      split at hu
      · simp at hu
      · simp only [List.mem_singleton] at hu
        subst hu; simp [stepLen]
  | H =>
    match t with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: t' =>
      intro u hu
      rw [enum1_H_cons] at hu
      split at hu
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> simp [stepLen]
      · simp only [List.mem_singleton] at hu
        subst hu; simp [stepLen]
  | A =>
    match t with
    | [] => simp
    | [_] => simp
    | e₁ :: e₂ :: t' =>
      intro u hu
      rw [enum1_A_cons] at hu
      split at hu
      · simp only [List.mem_singleton] at hu
        subst hu
        cases t' with
        | nil => simp [stepLen, sub2ifgt2]
        | cons c t'' => simp [stepLen, sub2ifgt2]
      · simp at hu

theorem foldList_nil_traces : ∀ cp : CProg, foldList cp [] = []
  | [] => rfl
  | s :: cp => by rw [foldList_cons, List.flatMap_nil]; exact foldList_nil_traces cp

theorem foldList_singleton_cons (s : CpStep) (cp : CProg) (t : List Color) :
    foldList (s :: cp) [t] = foldList cp (enum1 s t) := by
  rw [foldList_cons]
  congr 1
  simp

/-- Running a program on a list of traces is running it on each of them. -/
theorem mem_foldList_iff (cp : CProg) : ∀ (ts : List (List Color)) (t : List Color),
    t ∈ foldList cp ts ↔ ∃ u ∈ ts, t ∈ foldList cp [u] := by
  intro ts
  induction ts with
  | nil => intro t; rw [foldList_nil_traces]; simp
  | cons u ts ih =>
    intro t
    have hsplit : foldList cp (u :: ts) = foldList cp [u] ++ foldList cp ts :=
      foldList_append cp [u] ts
    rw [hsplit, List.mem_append]
    simp only [List.mem_cons, ih]
    constructor
    · rintro (h | ⟨v, hv, hvt⟩)
      · exact ⟨u, Or.inl rfl, h⟩
      · exact ⟨v, Or.inr hv, hvt⟩
    · rintro ⟨v, rfl | hv, hvt⟩
      · exact Or.inl hvt
      · exact Or.inr ⟨v, hv, hvt⟩

/-- The ring length after running `cp` (head first) from a ring of length `n`. -/
def cprsizeFrom : CProg → ℕ → ℕ
  | [], n => n
  | s :: cp, n => cprsizeFrom cp (stepLen s n)

theorem cprsizeFrom_append : ∀ (cp₁ cp₂ : CProg) (n : ℕ),
    cprsizeFrom (cp₁ ++ cp₂) n = cprsizeFrom cp₂ (cprsizeFrom cp₁ n)
  | [], _, _ => rfl
  | s :: cp₁, cp₂, n => by
      rw [List.cons_append, cprsizeFrom, cprsizeFrom, cprsizeFrom_append]

/-- The ring size of `cp` is the length the reversed program builds up from the
initial edge. -/
theorem cprsize_eq_cprsizeFrom : ∀ cp : CProg, cprsize cp = cprsizeFrom cp.reverse 2
  | [] => rfl
  | s :: cp => by
      rw [List.reverse_cons, cprsizeFrom_append, ← cprsize_eq_cprsizeFrom cp]
      cases s <;> rfl

/-- Run a whole program on a bulk state, head first. -/
def bulkFold : CProg → ℕ × List ℕ × ℕ → ℕ × List ℕ × ℕ
  | [], st => st
  | s :: cp, st => bulkFold cp (bulkStep s st)

@[simp] theorem bulkFold_nil (st : ℕ × List ℕ × ℕ) : bulkFold [] st = st := rfl

@[simp] theorem bulkFold_cons (s : CpStep) (cp : CProg) (st : ℕ × List ℕ × ℕ) :
    bulkFold (s :: cp) st = bulkFold cp (bulkStep s st) := rfl

/-- **The exactness of the bulk fold.**  The bits of the folded mask are
exactly the traces `foldList` enumerates from the traces of the bits of the
starting mask. -/
theorem testBit_bulkFold (cp : CProg) : ∀ (M : ℕ) (order : List ℕ) (S : ℕ), Good M order S →
    Good (bulkFold cp (M, order, S)).1 (bulkFold cp (M, order, S)).2.1
        (bulkFold cp (M, order, S)).2.2 ∧
      (bulkFold cp (M, order, S)).2.2 = cprsizeFrom cp S ∧
      ∀ j, j < 3 ^ (bulkFold cp (M, order, S)).2.2 →
        ((bulkFold cp (M, order, S)).1.testBit j = true ↔
          ∃ i, M.testBit i = true ∧
            slotTrace (bulkFold cp (M, order, S)).2.1 j ∈ foldList cp [slotTrace order i]) := by
  induction cp with
  | nil =>
    intro M order S hgood
    refine ⟨hgood, rfl, fun j hj => ?_⟩
    simp only [bulkFold_nil, foldList_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨j, h, rfl⟩
    · rintro ⟨i, hbi, he⟩
      rw [hgood.inj hj (hgood.bit_lt i hbi) he]; exact hbi
  | cons s cp ih =>
    intro M order S hgood
    obtain ⟨hg1, hS1, hspec1⟩ := bulkStep_spec s hgood
    obtain ⟨hg2, hS2, hspec2⟩ := ih _ _ _ hg1
    have heta : bulkFold (s :: cp) (M, order, S)
        = bulkFold cp ((bulkStep s (M, order, S)).1, (bulkStep s (M, order, S)).2.1,
            (bulkStep s (M, order, S)).2.2) := rfl
    rw [heta]
    refine ⟨hg2, ?_, fun j hj => ?_⟩
    · rw [hS2, hS1]
      rfl
    rw [hspec2 j hj]
    constructor
    · rintro ⟨i₁, hbi₁, hmem₁⟩
      obtain ⟨i, hbi, hmem⟩ := (hspec1 i₁ (hg1.bit_lt i₁ hbi₁)).mp hbi₁
      refine ⟨i, hbi, ?_⟩
      rw [foldList_singleton_cons, mem_foldList_iff]
      exact ⟨_, hmem, hmem₁⟩
    · rintro ⟨i, hbi, hmem⟩
      rw [foldList_singleton_cons, mem_foldList_iff] at hmem
      obtain ⟨u, hu, hfu⟩ := hmem
      have hulen : u.length = (bulkStep s (M, order, S)).2.2 := by
        rw [hS1, ← hgood.len, ← length_slotTrace order i]
        exact length_enum1 s _ u hu
      have hu0 : (0 : Color) ∉ u :=
        zero_notMem_enum1 s _ (zero_notMem_slotTrace order i) u hu
      have hmk : slotTrace (bulkStep s (M, order, S)).2.1
          (mkIndex (bulkStep s (M, order, S)).2.1 u) = u :=
        slotTrace_mkIndex hg1.nodup u (by rw [hulen, hg1.len]) hu0
      refine ⟨mkIndex (bulkStep s (M, order, S)).2.1 u, ?_, ?_⟩
      · exact (hspec1 _ (mkIndex_lt hg1.slot_lt u)).mpr ⟨i, hbi, by rw [hmk]; exact hu⟩
      · rw [hmk]; exact hfu

/-! ### Bringing the slots to a canonical layout

A permutation of the slots is a sequence of exchanges, one per ring position.
`alignMask S target order M` performs them, so that the mask it returns reads
in the layout `target` what `M` read in the layout `order`. -/

theorem swapIdx_swapIdx {S s t i : ℕ} (hs : s < S) (ht : t < S) (hi : i < 3 ^ S) :
    swapIdx s t (swapIdx s t i) = i := by
  refine digits_ext (swapIdx_lt hs ht (swapIdx_lt hs ht hi)) hi fun r => ?_
  rw [digit_swapIdx, digit_swapIdx, tau_tau]

/-- Relabel the slots of `order` so that the head becomes `target`'s head. -/
def alignMask (S : ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | t :: ts, s :: os, M =>
      if s = t then alignMask S ts os M
      else alignMask S ts (os.map (tau s t)) (swapAll S s t M)
  | _, _, M => M

theorem alignMask_cons_eq (S t : ℕ) (ts os : List ℕ) (M : ℕ) :
    alignMask S (t :: ts) (t :: os) M = alignMask S ts os M := by
  change (if t = t then alignMask S ts os M
    else alignMask S ts (os.map (tau t t)) (swapAll S t t M)) = _
  rw [ite_eq_left rfl]

theorem alignMask_cons_ne {S s t : ℕ} (hst : s ≠ t) (ts os : List ℕ) (M : ℕ) :
    alignMask S (t :: ts) (s :: os) M = alignMask S ts (os.map (tau s t)) (swapAll S s t M) := by
  change (if s = t then alignMask S ts os M
    else alignMask S ts (os.map (tau s t)) (swapAll S s t M)) = _
  rw [ite_eq_right hst]

theorem perm_map_tau {s t : ℕ} {os ts : List ℕ} (hst : s ≠ t)
    (hperm : (s :: os).Perm (t :: ts)) (hnd : (s :: os).Nodup) :
    (os.map (tau s t)).Perm ts := by
  have hndt : (t :: ts).Nodup := hperm.nodup hnd
  have hsts : s ∈ ts := by
    rcases List.mem_cons.mp (hperm.subset List.mem_cons_self) with h | h
    · exact absurd h hst
    · exact h
  have h1 : os.Perm (t :: ts.erase s) := by
    have h := (List.cons_perm_iff_perm_erase.mp hperm).2
    rwa [List.erase_cons_tail (by simpa using Ne.symm hst)] at h
  have h2 : (t :: ts.erase s).map (tau s t) = s :: ts.erase s := by
    rw [List.map_cons, tau_right (Ne.symm hst)]
    congr 1
    have hid : ∀ y ∈ ts.erase s, tau s t y = id y := by
      intro y hy
      have hys : y ≠ s := ((List.Nodup.mem_erase_iff hndt.of_cons).mp hy).1
      have hyt : y ≠ t := fun h => (List.nodup_cons.mp hndt).1 (h ▸ List.erase_subset hy)
      exact tau_of_ne hys hyt
    rw [List.map_congr_left hid, List.map_id]
  have h3 : ((t :: ts.erase s).map (tau s t)).Perm ts := by
    rw [h2]
    exact (List.perm_cons_erase hsts).symm
  exact (h1.map (tau s t)).trans h3

/-- The aligned mask reads in the layout `target` exactly what `M` reads in the
layout `order`. -/
theorem alignMask_spec (S : ℕ) : ∀ (target order : List ℕ), order.Perm target → order.Nodup →
    (∀ s ∈ order, s < S) → ∀ (M j : ℕ), j < 3 ^ S →
    ((alignMask S target order M).testBit j = true ↔
      ∃ i, i < 3 ^ S ∧ M.testBit i = true ∧ slotTrace target j = slotTrace order i ∧
        ∀ r, r ∉ order → digit r i = digit r j) := by
  intro target
  induction target with
  | nil =>
    intro order hperm _ _ M j hj
    have ho : order = [] := List.perm_nil.mp hperm
    subst ho
    change M.testBit j = true ↔ _
    constructor
    · intro h; exact ⟨j, hj, h, rfl, fun _ _ => rfl⟩
    · rintro ⟨i, hi, hbi, -, hdig⟩
      have hij : i = j := digits_ext hi hj fun r => hdig r (by simp)
      rw [← hij]; exact hbi
  | cons t ts ih =>
    intro order hperm hnd hlt M j hj
    cases order with
    | nil => exact absurd (List.perm_nil.mp hperm.symm) (by simp)
    | cons s os =>
      have hndos : os.Nodup := (List.nodup_cons.mp hnd).2
      have hsos : s ∉ os := (List.nodup_cons.mp hnd).1
      have hs : s < S := hlt s List.mem_cons_self
      have hltos : ∀ x ∈ os, x < S := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
      by_cases hst : s = t
      · subst hst
        rw [alignMask_cons_eq, ih os (List.Perm.cons_inv hperm) hndos hltos M j hj]
        constructor
        · rintro ⟨i, hi, hbi, hT, hdig⟩
          refine ⟨i, hi, hbi, ?_, fun r hr => hdig r fun h => hr (List.mem_cons_of_mem _ h)⟩
          rw [slotTrace_cons, slotTrace_cons, hT, hdig s hsos]
        · rintro ⟨i, hi, hbi, hT, hdig⟩
          rw [slotTrace_cons, slotTrace_cons, List.cons.injEq] at hT
          refine ⟨i, hi, hbi, hT.2, fun r hr => ?_⟩
          by_cases hrs : r = s
          · rw [hrs]
            exact (colourOfDigit_inj (digit_lt _ _) (digit_lt _ _) hT.1).symm
          · refine hdig r fun h => ?_
            rcases List.mem_cons.mp h with h' | h'
            · exact hrs h'
            · exact hr h'
      · have htmem : t ∈ s :: os := hperm.symm.subset List.mem_cons_self
        have ht : t < S := hlt t htmem
        have htos : t ∈ os := by
          rcases List.mem_cons.mp htmem with h | h
          · exact absurd h.symm hst
          · exact h
        have hperm' : (os.map (tau s t)).Perm ts := perm_map_tau hst hperm hnd
        have hnd' : (os.map (tau s t)).Nodup := hndos.map (tau_injective _ _)
        have hlt' : ∀ x ∈ os.map (tau s t), x < S := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          unfold tau
          split_ifs
          · exact ht
          · exact hs
          · exact hltos y hy
        have htnot : t ∉ os.map (tau s t) := by
          intro hx
          obtain ⟨y, hy, hxe⟩ := List.mem_map.mp hx
          have hys : y = s := by
            have h := congrArg (tau s t) hxe
            rwa [tau_tau, tau_right (Ne.symm hst)] at h
          exact hsos (hys ▸ hy)
        have hsin : s ∈ os.map (tau s t) := by
          refine List.mem_map.mpr ⟨t, htos, ?_⟩
          rw [tau_right (Ne.symm hst)]
        rw [alignMask_cons_ne hst, ih _ hperm' hnd' hlt' _ j hj]
        constructor
        · rintro ⟨i', hi', hbi', hT, hdig⟩
          rw [testBit_swapAll hs ht hst, Bool.and_eq_true, decide_eq_true_eq] at hbi'
          refine ⟨swapIdx s t i', swapIdx_lt hs ht hi', hbi'.2, ?_, fun r hr => ?_⟩
          · rw [slotTrace_cons, slotTrace_cons, slotTrace_swapIdx, hT, digit_swapIdx, tau_left,
              hdig t htnot]
          · have hrs : r ≠ s := fun h => hr (h ▸ List.mem_cons_self)
            have hrt : r ≠ t := fun h => hr (List.mem_cons_of_mem _ (h ▸ htos))
            rw [digit_swapIdx, tau_of_ne hrs hrt]
            refine hdig r fun hx => ?_
            obtain ⟨y, hy, hxe⟩ := List.mem_map.mp hx
            have hyr : y = r := by
              have h := congrArg (tau s t) hxe
              rwa [tau_tau, tau_of_ne hrs hrt] at h
            exact hr (List.mem_cons_of_mem _ (hyr ▸ hy))
        · rintro ⟨i, hi, hbi, hT, hdig⟩
          rw [slotTrace_cons, slotTrace_cons, List.cons.injEq] at hT
          refine ⟨swapIdx s t i, swapIdx_lt hs ht hi, ?_, ?_, fun r hr => ?_⟩
          · rw [testBit_swapAll hs ht hst, swapIdx_swapIdx hs ht hi]
            simp [swapIdx_lt hs ht hi, hbi]
          · rw [← slotTrace_swapIdx, swapIdx_swapIdx hs ht hi]
            exact hT.2
          · have hrs : r ≠ s := fun h => hr (h ▸ hsin)
            rw [digit_swapIdx]
            by_cases hrt : r = t
            · rw [hrt, tau_right (Ne.symm hst), ← hrt]
              exact (colourOfDigit_inj (digit_lt _ _) (digit_lt _ _) (hrt ▸ hT.1)).symm
            · rw [tau_of_ne hrs hrt]
              refine hdig r fun h => ?_
              rcases List.mem_cons.mp h with h' | h'
              · exact hrs h'
              · exact hr (List.mem_map.mpr ⟨r, h', tau_of_ne hrs hrt⟩)

/-! ### Projecting away the head position -/

/-- Drop the top digit, keeping every index below `3 ^ m` whose completion by
some top digit is in `M`. -/
def project (m M : ℕ) : ℕ :=
  (M &&& sel (m + 1) m 0) ||| ((M &&& sel (m + 1) m 1) >>> 3 ^ m)
    ||| ((M &&& sel (m + 1) m 2) >>> (2 * 3 ^ m))

theorem testBit_project (m M j : ℕ) (hj : j < 3 ^ m) :
    ((project m M).testBit j = true ↔ ∃ d, d < 3 ∧ M.testBit (setDigit m d j) = true) := by
  have hm : m < m + 1 := by omega
  have hpow : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [Nat.pow_succ]; ring
  have hsd : ∀ d : ℕ, setDigit m d j = d * 3 ^ m + j := by
    intro d
    unfold setDigit
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.mod_eq_of_lt hj]
    ring
  have hdig : ∀ d : ℕ, d < 3 → digit m (d * 3 ^ m + j) = d := by
    intro d hd
    rw [show d * 3 ^ m + j = 0 * 3 ^ (m + 1) + d * 3 ^ m + j by ring, digit_of_decomp hd hj]
  have hlt : ∀ d : ℕ, d < 3 → d * 3 ^ m + j < 3 ^ (m + 1) := by
    intro d hd
    rw [hpow]
    have : d * 3 ^ m ≤ 2 * 3 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega
  simp only [project, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight,
    testBit_sel hm 0 (by norm_num), testBit_sel hm 1 (by norm_num),
    testBit_sel hm 2 (by norm_num), Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((⟨hb, -⟩ | ⟨hb, -⟩) | ⟨hb, -⟩)
    · exact ⟨0, by norm_num, by rw [hsd]; simpa using hb⟩
    · exact ⟨1, by norm_num, by rw [hsd]; simpa using hb⟩
    · exact ⟨2, by norm_num, by rw [hsd]; simpa using hb⟩
  · rintro ⟨d, hd, hb⟩
    rw [hsd] at hb
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨by simpa using hb,
        lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)),
        by simpa using hdig 0 (by norm_num)⟩)
    · exact Or.inl (Or.inr ⟨by simpa using hb, by simpa using hlt 1 (by norm_num),
        by simpa using hdig 1 (by norm_num)⟩)
    · exact Or.inr ⟨hb, hlt 2 (by norm_num), hdig 2 (by norm_num)⟩

/-! ### The whole computation -/

/-- The bulk state `finalTraces` corresponds to, for a reversed program. -/
def bulkFinalState : CProg → ℕ × List ℕ × ℕ
  | .R _ :: rp => bulkFinalState rp
  | .Y :: rp => bulkFold rp (2 ^ 21, [0, 1, 2], 3)
  | .U :: rp => bulkFold rp (2 ^ 36 ||| 1, [0, 1, 2, 3], 4)
  | rp => bulkFold rp (1, [0, 1], 2)

/-- What the bulk computation of `finalTraces` achieves. -/
def FinalOK (rp : CProg) (M : ℕ) (order : List ℕ) (S : ℕ) : Prop :=
  Good M order S ∧ S = cprsizeFrom rp 2 ∧
    ∀ j, j < 3 ^ S → (M.testBit j = true ↔ slotTrace order j ∈ finalTraces rp)

theorem finalOK_of_fold {rp' rp : CProg} {M : ℕ} {order : List ℕ} {S : ℕ}
    {ts : List (List Color)} (hgood : Good M order S)
    (hstart : ∀ t : List Color, (∃ i, M.testBit i = true ∧ t = slotTrace order i) ↔ t ∈ ts)
    (hfinal : finalTraces rp' = foldList rp ts)
    (hsize : cprsizeFrom rp' 2 = cprsizeFrom rp S) :
    FinalOK rp' (bulkFold rp (M, order, S)).1 (bulkFold rp (M, order, S)).2.1
      (bulkFold rp (M, order, S)).2.2 := by
  obtain ⟨hg, hS, hspec⟩ := testBit_bulkFold rp M order S hgood
  refine ⟨hg, by rw [hS, hsize], fun j hj => ?_⟩
  rw [hspec j hj, hfinal, mem_foldList_iff]
  constructor
  · rintro ⟨i, hbi, hmem⟩
    exact ⟨slotTrace order i, (hstart _).mp ⟨i, hbi, rfl⟩, hmem⟩
  · rintro ⟨u, hu, hfu⟩
    obtain ⟨i, hbi, rfl⟩ := (hstart u).mpr hu
    exact ⟨i, hbi, hfu⟩

theorem good_base2 : Good 1 [0, 1] 2 where
  nodup := by decide
  slot_lt := by decide
  len := rfl
  pos := by norm_num
  bit_lt := by
    intro i hi
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hi
    subst hi
    norm_num

theorem good_base3 : Good (2 ^ 21) [0, 1, 2] 3 where
  nodup := by decide
  slot_lt := by decide
  len := rfl
  pos := by norm_num
  bit_lt := by
    intro i hi
    rw [Nat.testBit_two_pow] at hi
    simp only [decide_eq_true_eq] at hi
    subst hi
    norm_num

theorem good_base4 : Good (2 ^ 36 ||| 1) [0, 1, 2, 3] 4 where
  nodup := by decide
  slot_lt := by decide
  len := rfl
  pos := by norm_num
  bit_lt := by
    intro i hi
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      Nat.testBit_one_eq_true_iff_self_eq_zero] at hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> norm_num

theorem base2_start (t : List Color) :
    (∃ i, (1 : ℕ).testBit i = true ∧ t = slotTrace [0, 1] i) ↔ t ∈ [[c1, c1]] := by
  constructor
  · rintro ⟨i, hbi, rfl⟩
    rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hbi
    subst hbi
    exact List.mem_cons_self
  · intro ht
    refine ⟨0, by rw [Nat.testBit_one_eq_true_iff_self_eq_zero], ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [ht]
    decide

theorem bulkFinalState_spec : ∀ rp : CProg,
    FinalOK rp (bulkFinalState rp).1 (bulkFinalState rp).2.1 (bulkFinalState rp).2.2
  | .R _ :: rp => bulkFinalState_spec rp
  | .Y :: rp => by
      refine finalOK_of_fold good_base3 (fun t => ?_) rfl rfl
      constructor
      · rintro ⟨i, hbi, rfl⟩
        rw [Nat.testBit_two_pow, decide_eq_true_eq] at hbi
        subst hbi
        exact List.mem_cons_self
      · intro ht
        refine ⟨21, by rw [Nat.testBit_two_pow]; simp, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rw [ht]
        decide
  | .U :: rp => by
      refine finalOK_of_fold good_base4 (fun t => ?_) (foldList_append rp _ _).symm rfl
      constructor
      · rintro ⟨i, hbi, rfl⟩
        rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
          Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_eq] at hbi
        rcases hbi with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      · intro ht
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at ht
        rcases ht with rfl | rfl
        · exact ⟨36, by decide, by decide⟩
        · exact ⟨0, by decide, by decide⟩
  | [] => by exact finalOK_of_fold good_base2 base2_start rfl rfl
  | .R' :: rp => by exact finalOK_of_fold good_base2 base2_start rfl rfl
  | .K :: rp => by exact finalOK_of_fold good_base2 base2_start rfl rfl
  | .H :: rp => by exact finalOK_of_fold good_base2 base2_start rfl rfl
  | .A :: rp => by exact finalOK_of_fold good_base2 base2_start rfl rfl

/-- The bulk computation of `finalTraces cp.reverse`: a mask over the indices
below `3 ^ m`, where `m + 1 = cprsize cp`.  Ring position `k + 1` sits at digit
`k`, and the head position, which sits at digit `m`, is projected away. -/
def bulkFinal (cp : CProg) : ℕ :=
  project ((bulkFinalState cp.reverse).2.2 - 1)
    (alignMask (bulkFinalState cp.reverse).2.2
      (((bulkFinalState cp.reverse).2.2 - 1) :: List.range ((bulkFinalState cp.reverse).2.2 - 1))
      (bulkFinalState cp.reverse).2.1 (bulkFinalState cp.reverse).1)

/-- **The bulk computation is exact.**  Bit `j` of `bulkFinal cp` is set exactly
when some trace the program enumerates has `partialOf m j` as its tail. -/
theorem testBit_bulkFinal (cp : CProg) (m : ℕ) (hm : cprsize cp = m + 1) (j : ℕ)
    (hj : j < 3 ^ m) :
    ((bulkFinal cp).testBit j = true ↔ ∃ t ∈ finalTraces cp.reverse, t.tail = partialOf m j) := by
  obtain ⟨hg, hS, hspec⟩ := bulkFinalState_spec cp.reverse
  have hSm : (bulkFinalState cp.reverse).2.2 = m + 1 := by
    rw [hS, ← cprsize_eq_cprsizeFrom, hm]
  have hlt : ∀ s ∈ (bulkFinalState cp.reverse).2.1, s < m + 1 := by
    rw [← hSm]; exact hg.slot_lt
  have hlen : (bulkFinalState cp.reverse).2.1.length = m + 1 := by rw [hg.len, hSm]
  have hndt : (m :: List.range m).Nodup :=
    List.nodup_cons.mpr ⟨by simp, List.nodup_range⟩
  have hperm : (bulkFinalState cp.reverse).2.1.Perm (m :: List.range m) := by
    rw [List.perm_ext_iff_of_nodup hg.nodup hndt]
    intro a
    constructor
    · intro ha
      have haa := hlt a ha
      rcases Nat.lt_or_ge a m with h | h
      · exact List.mem_cons_of_mem _ (List.mem_range.mpr h)
      · rw [show a = m by omega]
        exact List.mem_cons_self
    · intro ha
      refine mem_of_lt_of_nodup hg.nodup hlt hlen ?_
      rcases List.mem_cons.mp ha with rfl | ha'
      · omega
      · have := List.mem_range.mp ha'; omega
  -- the aligned mask reads the canonical layout
  have halign : ∀ j', j' < 3 ^ (m + 1) →
      ((alignMask (m + 1) (m :: List.range m) (bulkFinalState cp.reverse).2.1
          (bulkFinalState cp.reverse).1).testBit j' = true ↔
        slotTrace (m :: List.range m) j' ∈ finalTraces cp.reverse) := by
    intro j' hj'
    rw [alignMask_spec (m + 1) (m :: List.range m) _ hperm hg.nodup hlt _ j' hj']
    constructor
    · rintro ⟨i, hi, hbi, hT, -⟩
      rw [hT]
      exact (hspec i (by rw [hSm]; exact hi)).mp hbi
    · intro ht
      have htlen : (slotTrace (m :: List.range m) j').length
          = (bulkFinalState cp.reverse).2.1.length := by
        rw [length_slotTrace, hlen, List.length_cons, List.length_range]
      have hmk := slotTrace_mkIndex hg.nodup (slotTrace (m :: List.range m) j') htlen
        (zero_notMem_slotTrace _ _)
      have hmklt : mkIndex (bulkFinalState cp.reverse).2.1
          (slotTrace (m :: List.range m) j') < 3 ^ (m + 1) := mkIndex_lt hlt _
      refine ⟨_, hmklt, ?_, hmk.symm, fun r hr => ?_⟩
      · refine (hspec _ (by rw [hSm]; exact hmklt)).mpr ?_
        rw [hmk]; exact ht
      · have hrS : m + 1 ≤ r := by
          by_contra hcon
          exact hr (mem_of_lt_of_nodup hg.nodup hlt hlen (by omega))
        rw [digit_eq_zero_of_lt hmklt hrS, digit_eq_zero_of_lt hj' hrS]
  -- the projection drops the head position
  have hsdlt : ∀ d, d < 3 → setDigit m d j < 3 ^ (m + 1) := fun d hd =>
    setDigit_lt (by omega) hd
      (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hst : ∀ d, d < 3 →
      slotTrace (m :: List.range m) (setDigit m d j) = colourOfDigit d :: partialOf m j := by
    intro d hd
    rw [slotTrace_cons, digit_setDigit_self hd]
    congr 1
    rw [slotTrace_setDigit_of_not_mem (by simp) hd]
    rfl
  unfold bulkFinal
  rw [hSm]
  simp only [Nat.add_sub_cancel]
  rw [testBit_project m _ j hj]
  constructor
  · rintro ⟨d, hd, hb⟩
    rw [halign _ (hsdlt d hd), hst d hd] at hb
    exact ⟨_, hb, rfl⟩
  · rintro ⟨t, ht, htail⟩
    have h2 := two_le_length_finalTraces _ t ht
    have h0 := zero_notMem_finalTraces _ t ht
    obtain ⟨c, t', rfl⟩ : ∃ c t', t = c :: t' := by
      cases t with
      | nil => simp at h2
      | cons c t' => exact ⟨c, t', rfl⟩
    have hc : c ≠ 0 := fun h => h0 (by simp [h])
    refine ⟨fdigitOf c, fdigitOf_lt c, ?_⟩
    rw [halign _ (hsdlt _ (fdigitOf_lt c)), hst _ (fdigitOf_lt c), colourOfDigit_fdigitOf c hc]
    simp only [List.tail_cons] at htail
    rw [← htail]
    exact ht

end Bulk
end FourColor

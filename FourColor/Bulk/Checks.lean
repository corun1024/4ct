import FourColor.Bulk.Kempe

/-!
# The decidable checks of a bulk certificate

The hypotheses of `hcert_of_bulk` about the choice planes and the pairs are
universally quantified over positions.  A generated module proves them as
`Bool` facts instead — one declaration per pair, so the kernel releases each
pair's workspace — and this file turns those facts back into the quantified
hypotheses.
-/

namespace FourColor
namespace Bulk

/-- The choice mask of a pair: the certified traces argued with `p` or `q`. -/
def pairChoice (m : ℕ) (R C : List ℕ) (p q : ℕ) : ℕ :=
  choiceMask m C (nonZero m R) p ||| choiceMask m C (nonZero m R) q

/-- The pairs `p < q ≤ m`, as a list. -/
def pairList (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (m + 1)).flatMap fun q => (List.range q).map fun p => (p, q)

theorem mem_pairList {m p q : ℕ} : (p, q) ∈ pairList m ↔ p < q ∧ q ≤ m := by
  unfold pairList
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq', p', hp', rfl, rfl⟩; omega
  · rintro ⟨hpq, hq⟩; exact ⟨q, by omega, p, hpq, rfl, rfl⟩

/-- Every pair check, as one boolean; a generated module proves it from the
individual pair theorems. -/
def allPairs (m : ℕ) (R H C : List ℕ) : Bool :=
  (pairList m).all fun pq => pairOk m pq.1 pq.2 R H (pairChoice m R C pq.1 pq.2)

theorem allPairs_spec {m : ℕ} {R H C : List ℕ} (h : allPairs m R H C = true) :
    ∀ p q, p < q → q ≤ m → pairOk m p q R H (pairChoice m R C p q) = true := by
  intro p q hpq hq
  unfold allPairs at h
  rw [List.all_eq_true] at h
  exact h (p, q) (mem_pairList.mpr ⟨hpq, hq⟩)

/-- The choice planes name a real chord end for every certified trace: a
position at all, and one holding `c2` or `c3`. -/
def choiceCheck (m : ℕ) (R C : List ℕ) : Bool :=
  ((List.range (m + 1)).all fun p =>
      (choiceMask m C (nonZero m R) p &&& ((2 ^ 3 ^ m - 1) ^^^ nonC1 m p)) == 0) &&
  ((List.range' (m + 1) (2 ^ C.length - (m + 1))).all fun p =>
      (nonZero m R &&& choiceMask m C (nonZero m R) p) == 0)

theorem choiceCheck_spec₁ {m : ℕ} {R C : List ℕ} (h : choiceCheck m R C = true) :
    ∀ p, p ≤ m → choiceMask m C (nonZero m R) p &&& ((2 ^ 3 ^ m - 1) ^^^ nonC1 m p) = 0 := by
  intro p hp
  unfold choiceCheck at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have := h.1 p (List.mem_range.mpr (by omega))
  simpa using this

theorem choiceCheck_spec₂ {m : ℕ} {R C : List ℕ} (hClen : m < 2 ^ C.length)
    (h : choiceCheck m R C = true) :
    ∀ i, i < 3 ^ m → (nonZero m R).testBit i = true → val C i ≤ m := by
  intro i hi hnz
  by_contra hgt
  unfold choiceCheck at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have hlt := val_lt_two_pow C i
  have hmem : val C i ∈ List.range' (m + 1) (2 ^ C.length - (m + 1)) := by
    rw [List.mem_range'_1]; omega
  have h2 := h.2 _ hmem
  simp only [beq_iff_eq] at h2
  have hbit := congrArg (fun x => x.testBit i) h2
  simp only [Nat.testBit_and, Nat.zero_testBit, hnz, Bool.true_and,
    testBit_choiceMask C _ _ i hi hlt] at hbit
  simp at hbit

end Bulk
end FourColor

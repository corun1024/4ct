import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card

/-!
# Adjoining one relation to an equivalence

Merging two classes of an equivalence relation drops the number of classes by
exactly one, precisely when the two elements were in different classes.  This is
the combinatorial core of the fact that multiplying a permutation by a
transposition changes its number of orbits by one, which in turn is what the
Euler formula for hypermaps rests on.

## Main definitions

* `Setoid.adjoin r a b` — the least equivalence containing `r` and the pair
  `(a, b)`, described explicitly.
* `Setoid.card_quotient_adjoin_of_not` — the class count drops by one.
-/

namespace FourColor

variable {D : Type*}

namespace Setoid

/-- The least equivalence containing `r` together with the pair `(a, b)`.  Since
only one pair is adjoined, it has an explicit description: `x` and `y` become
related exactly when they already were, or when one is `r`-related to `a` and
the other to `b`. -/
def adjoin (r : Setoid D) (a b : D) : Setoid D where
  r x y := r x y ∨ (r x a ∧ r y b) ∨ (r x b ∧ r y a)
  iseqv := by
    refine ⟨fun x => Or.inl (r.refl' x), ?_, ?_⟩
    · rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl (r.symm' h)
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
      · exact Or.inr (Or.inl ⟨h2, h1⟩)
    · rintro x y z (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) (k | ⟨k1, k2⟩ | ⟨k1, k2⟩)
      · exact Or.inl (r.trans' h k)
      · exact Or.inr (Or.inl ⟨r.trans' h k1, k2⟩)
      · exact Or.inr (Or.inr ⟨r.trans' h k1, k2⟩)
      · exact Or.inr (Or.inl ⟨h1, r.trans' (r.symm' k) h2⟩)
      · exact Or.inl (r.trans' (r.trans' h1 (r.symm' (r.trans' (r.symm' h2) k1)))
          (r.symm' k2))
      · exact Or.inl (r.trans' h1 (r.symm' k2))
      · exact Or.inr (Or.inr ⟨h1, r.trans' (r.symm' k) h2⟩)
      · exact Or.inl (r.trans' h1 (r.symm' k2))
      · exact Or.inl (r.trans' (r.trans' h1 (r.symm' (r.trans' (r.symm' h2) k1)))
          (r.symm' k2))

theorem adjoin_rel (r : Setoid D) (a b : D) : (adjoin r a b) a b :=
  Or.inr (Or.inl ⟨r.refl' a, r.refl' b⟩)

theorem le_adjoin (r : Setoid D) (a b : D) {x y : D} (h : r x y) : (adjoin r a b) x y :=
  Or.inl h

theorem adjoin_iff (r : Setoid D) (a b : D) (x y : D) :
    (adjoin r a b) x y ↔ (r x y ∨ (r x a ∧ r y b) ∨ (r x b ∧ r y a)) := Iff.rfl

end Setoid

/-- Removing one element from a finite type drops its cardinality by one. -/
theorem card_subtype_ne_add_one {α : Type*} [Finite α] (b : α) :
    Nat.card {x : α // x ≠ b} + 1 = Nat.card α := by
  classical
  have hbij : Function.Bijective
      (fun o : Option {x : α // x ≠ b} => o.elim b Subtype.val) := by
    constructor
    · rintro (_ | p) (_ | q) h
      · rfl
      · exact absurd h.symm q.2
      · exact absurd h p.2
      · exact congrArg some (Subtype.ext h)
    · intro x
      by_cases hx : x = b
      · exact ⟨none, hx.symm⟩
      · exact ⟨some ⟨x, hx⟩, rfl⟩
  have hc := Nat.card_eq_of_bijective _ hbij
  rw [Finite.card_option] at hc
  omega

namespace Setoid

/-- If the two elements were already related, merging changes nothing. -/
theorem adjoin_eq_of {r : Setoid D} {a b : D} (hab : r a b) (x y : D) :
    (adjoin r a b) x y ↔ r x y := by
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    · exact r.trans' h1 (r.trans' hab (r.symm' h2))
    · exact r.trans' h1 (r.trans' (r.symm' hab) (r.symm' h2))
  · exact Or.inl

/-- `adjoin r a b` is the *least* equivalence containing `r` and the pair
`(a, b)`: any equivalence that does is coarser. -/
theorem adjoin_le {r q : Setoid D} {a b : D} (hrq : ∀ x y, r x y → q x y)
    (hab : q a b) {x y : D} (h : (adjoin r a b) x y) : q x y := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hrq _ _ h
  · exact q.trans' (hrq _ _ h1) (q.trans' hab (q.symm' (hrq _ _ h2)))
  · exact q.trans' (hrq _ _ h1) (q.trans' (q.symm' hab) (q.symm' (hrq _ _ h2)))

/-- Adjoining a pair that is already related changes nothing. -/
theorem adjoin_eq_self_of {r : Setoid D} {a b : D} (hab : r a b) :
    adjoin r a b = r :=
  Setoid.ext (adjoin_eq_of hab)

variable [Finite D]

/-- Merging two classes of an equivalence drops the number of classes by
exactly one. -/
theorem card_quotient_adjoin_of_not {r : Setoid D} {a b : D} (hab : ¬ r a b) :
    Nat.card (Quotient (adjoin r a b)) + 1 = Nat.card (Quotient r) := by
  classical
  have hne : ∀ x : D, ¬ r x b → (Quotient.mk r x) ≠ Quotient.mk r b :=
    fun x hx hc => hx (Quotient.exact hc)
  have hane : (Quotient.mk r a) ≠ Quotient.mk r b := hne a hab
  -- the map sending a class of the merged relation to a class of `r` other than `⟦b⟧`
  let f : D → {q : Quotient r // q ≠ Quotient.mk r b} := fun x =>
    if hx : r x b then ⟨Quotient.mk r a, hane⟩ else ⟨Quotient.mk r x, hne x hx⟩
  have hwd : ∀ x y : D, (adjoin r a b) x y → f x = f y := by
    rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · by_cases hx : r x b
      · have hy : r y b := r.trans' (r.symm' h) hx
        simp only [f, dite_eq_left hx, dite_eq_left hy]
      · have hy : ¬ r y b := fun hc => hx (r.trans' h hc)
        simp only [f, dite_eq_right hx, dite_eq_right hy]
        exact Subtype.ext (Quotient.sound h)
    · have hx : ¬ r x b := fun hc => hab (r.trans' (r.symm' h1) hc)
      simp only [f, dite_eq_right hx, dite_eq_left h2]
      exact Subtype.ext (Quotient.sound h1)
    · have hy : ¬ r y b := fun hc => hab (r.trans' (r.symm' h2) hc)
      simp only [f, dite_eq_left h1, dite_eq_right hy]
      exact Subtype.ext (Quotient.sound (r.symm' h2))
  have hbij : Function.Bijective (@Quotient.lift D _ (adjoin r a b) f hwd) := by
    constructor
    · refine fun u v => Quotient.inductionOn₂ u v fun x y hxy => ?_
      simp only [Quotient.lift_mk] at hxy
      refine Quotient.sound ?_
      by_cases hx : r x b
      · by_cases hy : r y b
        · exact Or.inl (r.trans' hx (r.symm' hy))
        · simp only [f, dite_eq_left hx, dite_eq_right hy, Subtype.mk.injEq] at hxy
          exact Or.inr (Or.inr ⟨hx, r.symm' (Quotient.exact hxy)⟩)
      · by_cases hy : r y b
        · simp only [f, dite_eq_right hx, dite_eq_left hy, Subtype.mk.injEq] at hxy
          exact Or.inr (Or.inl ⟨Quotient.exact hxy, hy⟩)
        · simp only [f, dite_eq_right hx, dite_eq_right hy, Subtype.mk.injEq] at hxy
          exact Or.inl (Quotient.exact hxy)
    · rintro ⟨q, hq⟩
      refine Quotient.inductionOn q (motive := fun q => ∀ hq : q ≠ Quotient.mk r b,
        ∃ u, (@Quotient.lift D _ (adjoin r a b) f hwd) u = ⟨q, hq⟩) ?_ hq
      intro x hx
      have hxb : ¬ r x b := fun hc => hx (Quotient.sound hc)
      exact ⟨Quotient.mk (adjoin r a b) x, by
        simp only [Quotient.lift_mk, f, dite_eq_right hxb]⟩
  rw [Nat.card_eq_of_bijective _ hbij]
  exact card_subtype_ne_add_one _

/-- The number of classes of an equivalence, in terms of the number of classes
after merging the classes of `a` and `b`. -/
theorem card_quotient_eq_card_quotient_adjoin
    (r : Setoid D) (a b : D) [Decidable (r a b)] :
    Nat.card (Quotient r)
      = Nat.card (Quotient (adjoin r a b)) + (if r a b then 0 else 1) := by
  by_cases hab : r a b
  · rw [ite_eq_left hab, adjoin_eq_self_of hab, Nat.add_zero]
  · rw [ite_eq_right hab]
    exact (card_quotient_adjoin_of_not hab).symm

end Setoid

end FourColor

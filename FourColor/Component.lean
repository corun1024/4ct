import FourColor.Adjoin
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Components under point deletion

Deleting one point from a graph changes the number of connected components in
one of three ways: the count drops by one if the point was isolated, stays the
same if its neighbourhood remains connected without it, and goes up by one if
the neighbourhood falls into two pieces.

The Walkup construction is of this shape but is not an induced subgraph: where
the original link relation steps onto the deleted dart, the derived one steps
over it, so a neighbour of `z` stays linked to the *next* dart rather than to
`z`.  `IsDeletion` axiomatises exactly what is needed of such a derived
relation, and the two theorems below express the component count of the original
in terms of the derived one — the second via `Setoid.adjoin`, so that the
split-or-not dichotomy is exactly whether the two attachment darts are already
connected.

## Main definitions

* `compSetoid r` — the components of `r`, its equivalence closure.
* `Attached r z x` — `x` is a neighbour of `z`.
* `IsDeletion r z s` — `s` is a link relation on the darts other than `z`
  realised by, and realising, `r`-links away from `z`.

## Main results

* `Deletion.card_comp_of_isolated` — an isolated point is a component of its
  own.
* `Deletion.card_comp_of_attached` — otherwise the components of `r` are the
  components of `s` with the two attachment classes merged.
-/

namespace FourColor

open Relation

variable {D : Type*} {z : D}

/-- The components of a relation: its equivalence closure. -/
def compSetoid (r : D → D → Prop) : Setoid D := ⟨EqvGen r, EqvGen.is_equivalence r⟩

theorem compSetoid_iff {r : D → D → Prop} {x y : D} :
    (compSetoid r) x y ↔ EqvGen r x y := Iff.rfl

/-- The darts other than `z`. -/
abbrev Deleted (z : D) : Type _ := {x : D // x ≠ z}

/-- `x` is a neighbour of `z`. -/
def Attached (r : D → D → Prop) (z x : D) : Prop := r z x ∨ r x z

theorem Attached.eqvGen {r : D → D → Prop} {x : D} (h : Attached r z x) :
    EqvGen r z x :=
  h.elim (EqvGen.rel _ _) fun h => EqvGen.symm _ _ (EqvGen.rel _ _ h)

/-- `s` links the darts other than `z` in a way `r` realises, and it links
everything `r` links away from `z`. -/
structure IsDeletion (r : D → D → Prop) (z : D)
    (s : Deleted z → Deleted z → Prop) : Prop where
  sound : ∀ u v : Deleted z, s u v → EqvGen r u.val v.val
  complete : ∀ u v : Deleted z, r u.val v.val → EqvGen s u v

namespace Deletion

variable {r : D → D → Prop} {s : Deleted z → Deleted z → Prop}

/-- Connectedness in the deleted relation is connectedness in the original. -/
theorem eqvGen_val (hs : IsDeletion r z s) {u v : Deleted z} (h : EqvGen s u v) :
    EqvGen r u.val v.val := by
  induction h with
  | rel x y hxy => exact hs.sound x y hxy
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y w _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

/-! ### An isolated point -/

section Isolated

/-- An isolated point is connected to nothing but itself. -/
theorem eq_of_eqvGen_isolated (hiso : ∀ y, Attached r z y → y = z) {x y : D}
    (h : EqvGen r x y) :
    (x = z → y = z) ∧ (y = z → x = z) := by
  induction h with
  | rel x y hxy =>
    exact ⟨fun hx => hiso y (Or.inl (hx ▸ hxy)), fun hy => hiso x (Or.inr (hy ▸ hxy))⟩
  | refl x => exact ⟨id, id⟩
  | symm x y _ ih => exact ⟨ih.2, ih.1⟩
  | trans x y w _ _ ih₁ ih₂ =>
    exact ⟨fun hx => ih₂.1 (ih₁.1 hx), fun hw => ih₁.2 (ih₂.2 hw)⟩

/-- Away from an isolated point, connectedness is unchanged by the deletion. -/
theorem eqvGen_of_eqvGen_val_isolated (hiso : ∀ y, Attached r z y → y = z)
    (hs : IsDeletion r z s) {x y : D}
    (h : EqvGen r x y) : ∀ (hx : x ≠ z) (hy : y ≠ z), EqvGen s ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | rel x y hxy => exact fun hx hy => hs.complete ⟨x, hx⟩ ⟨y, hy⟩ hxy
  | refl x => exact fun hx _ => EqvGen.refl _
  | symm x y _ ih => exact fun hx hy => EqvGen.symm _ _ (ih hy hx)
  | @trans x y w hxy _ ih₁ ih₂ =>
    intro hx hw
    have hy : y ≠ z := fun hyz => hx ((eq_of_eqvGen_isolated hiso hxy).2 hyz)
    exact EqvGen.trans _ _ _ (ih₁ hx hy) (ih₂ hy hw)

/-- Deleting an isolated point removes a component. -/
theorem card_comp_of_isolated [Finite D] (hiso : ∀ y, Attached r z y → y = z)
    (hs : IsDeletion r z s) :
    Nat.card (Quotient (compSetoid r)) = Nat.card (Quotient (compSetoid s)) + 1 := by
  have hwd : ∀ u v : Deleted z, (compSetoid s) u v →
      Quotient.mk (compSetoid r) u.val = Quotient.mk (compSetoid r) v.val :=
    fun _ _ h => Quotient.sound (eqvGen_val hs h)
  let F : Option (Quotient (compSetoid s)) → Quotient (compSetoid r) := fun o =>
    o.elim (Quotient.mk (compSetoid r) z)
      (Quotient.lift (fun u : Deleted z => Quotient.mk (compSetoid r) u.val) hwd)
  have hFnone : F none = Quotient.mk (compSetoid r) z := rfl
  have hbij : Function.Bijective F := by
    constructor
    · intro o o' h
      match o, o' with
      | none, none => rfl
      | none, some q =>
        refine q.inductionOn (motive := fun q => F none = F (some q) → none = some q) ?_ h
        intro u hu
        exact absurd ((eq_of_eqvGen_isolated hiso (Quotient.exact hu)).1 rfl) u.2
      | some q, none =>
        refine q.inductionOn (motive := fun q => F (some q) = F none → some q = none) ?_ h
        intro u hu
        exact absurd ((eq_of_eqvGen_isolated hiso (Quotient.exact hu)).2 rfl) u.2
      | some q, some q' =>
        refine Quotient.inductionOn₂ q q'
          (motive := fun q q' => F (some q) = F (some q') → some q = some q') ?_ h
        intro u v huv
        exact congrArg some (Quotient.sound
          (eqvGen_of_eqvGen_val_isolated hiso hs (Quotient.exact huv) u.2 v.2))
    · refine fun q => q.inductionOn fun x => ?_
      by_cases hx : x = z
      · exact ⟨none, by rw [hFnone, hx]⟩
      · exact ⟨some (Quotient.mk (compSetoid s) ⟨x, hx⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective F hbij, Finite.card_option]

end Isolated

/-! ### A point with neighbours -/

section Attached

variable {a b : Deleted z}

/-- The two attachment darts are connected in the original relation, through
the deleted point. -/
theorem eqvGen_attach (ha : Attached r z a.val) (hb : Attached r z b.val) :
    EqvGen r a.val b.val :=
  EqvGen.trans _ _ _ (EqvGen.symm _ _ ha.eqvGen) hb.eqvGen

/-- Merging the two attachment classes does not add connections. -/
theorem eqvGen_of_adjoin (hs : IsDeletion r z s) (ha : Attached r z a.val)
    (hb : Attached r z b.val) {u v : Deleted z}
    (h : (Setoid.adjoin (compSetoid s) a b) u v) : EqvGen r u.val v.val := by
  rcases h with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact eqvGen_val hs h
  · exact EqvGen.trans _ _ _ (eqvGen_val hs h₁)
      (EqvGen.trans _ _ _ (eqvGen_attach ha hb) (EqvGen.symm _ _ (eqvGen_val hs h₂)))
  · exact EqvGen.trans _ _ _ (eqvGen_val hs h₁)
      (EqvGen.trans _ _ _ (EqvGen.symm _ _ (eqvGen_attach ha hb))
        (EqvGen.symm _ _ (eqvGen_val hs h₂)))

open scoped Classical in
/-- Classifying a dart by its class after the merge, with the deleted point
assigned to the class of the first attachment dart. -/
noncomputable def toAdjoin (s : Deleted z → Deleted z → Prop) (a b : Deleted z)
    (x : D) : Quotient (Setoid.adjoin (compSetoid s) a b) :=
  if hx : x = z then Quotient.mk _ a else Quotient.mk _ ⟨x, hx⟩

theorem toAdjoin_of_ne {x : D} (hx : x ≠ z) :
    toAdjoin s a b x = Quotient.mk _ ⟨x, hx⟩ := by
  simp only [toAdjoin, dite_eq_right hx]

theorem toAdjoin_self : toAdjoin s a b z = Quotient.mk _ a := by
  simp [toAdjoin]

/-- A neighbour of the deleted point falls in the merged class. -/
theorem toAdjoin_attached
    (hab : ∀ u : Deleted z, Attached r z u.val → EqvGen s u a ∨ EqvGen s u b)
    {u : Deleted z} (hu : Attached r z u.val) :
    toAdjoin s a b u.val = Quotient.mk _ a := by
  rw [toAdjoin_of_ne u.2]
  rcases hab u hu with h | h
  · exact Quotient.sound (Setoid.le_adjoin _ a b h)
  · exact Quotient.sound ((Setoid.adjoin (compSetoid s) a b).trans'
      (Setoid.le_adjoin _ a b h) ((Setoid.adjoin (compSetoid s) a b).symm'
        (Setoid.adjoin_rel (compSetoid s) a b)))

theorem toAdjoin_eq_of_eqvGen (hs : IsDeletion r z s)
    (hab : ∀ u : Deleted z, Attached r z u.val → EqvGen s u a ∨ EqvGen s u b)
    {x y : D} (h : EqvGen r x y) : toAdjoin s a b x = toAdjoin s a b y := by
  induction h with
  | rel x y hxy =>
    by_cases hx : x = z
    · by_cases hy : y = z
      · rw [hx, hy]
      · rw [hx, toAdjoin_self, toAdjoin_attached hab (u := ⟨y, hy⟩) (Or.inl (hx ▸ hxy))]
    · by_cases hy : y = z
      · rw [hy, toAdjoin_self, toAdjoin_attached hab (u := ⟨x, hx⟩) (Or.inr (hy ▸ hxy))]
      · rw [toAdjoin_of_ne hx, toAdjoin_of_ne hy]
        exact Quotient.sound (Setoid.le_adjoin _ a b
          (hs.complete ⟨x, hx⟩ ⟨y, hy⟩ hxy))
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y w _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Deleting a point with neighbours leaves the components of the original as
the components of the deletion with the two attachment classes merged. -/
theorem card_comp_of_attached [Finite D] (hs : IsDeletion r z s)
    (ha : Attached r z a.val) (hb : Attached r z b.val)
    (hab : ∀ u : Deleted z, Attached r z u.val → EqvGen s u a ∨ EqvGen s u b) :
    Nat.card (Quotient (compSetoid r))
      = Nat.card (Quotient (Setoid.adjoin (compSetoid s) a b)) := by
  have hwd : ∀ x y : D, (compSetoid r) x y →
      toAdjoin s a b x = toAdjoin s a b y :=
    fun _ _ h => toAdjoin_eq_of_eqvGen hs hab h
  have hbij : Function.Bijective
      (@Quotient.lift D _ (compSetoid r) (toAdjoin s a b) hwd) := by
    constructor
    · refine fun q q' => Quotient.inductionOn₂ q q' fun x y hxy => ?_
      simp only [Quotient.lift_mk] at hxy
      refine Quotient.sound ?_
      by_cases hx : x = z
      · by_cases hy : y = z
        · rw [hx, hy]
        · rw [hx, toAdjoin_self, toAdjoin_of_ne hy] at hxy
          rw [hx]
          exact EqvGen.trans _ _ _ ha.eqvGen
            (eqvGen_of_adjoin hs ha hb (Quotient.exact hxy))
      · by_cases hy : y = z
        · rw [hy, toAdjoin_self, toAdjoin_of_ne hx] at hxy
          rw [hy]
          exact EqvGen.trans _ _ _ (eqvGen_of_adjoin hs ha hb (Quotient.exact hxy))
            (EqvGen.symm _ _ ha.eqvGen)
        · rw [toAdjoin_of_ne hx, toAdjoin_of_ne hy] at hxy
          exact eqvGen_of_adjoin hs ha hb (Quotient.exact hxy)
    · refine fun q => q.inductionOn fun u => ?_
      exact ⟨Quotient.mk (compSetoid r) u.val, by
        simp only [Quotient.lift_mk, toAdjoin_of_ne u.2]⟩
  exact Nat.card_eq_of_bijective _ hbij

/-- If the whole neighbourhood of the deleted point stays connected, the
component count is unchanged. -/
theorem card_comp_of_attached_single [Finite D] (hs : IsDeletion r z s)
    (ha : Attached r z a.val)
    (hab : ∀ u : Deleted z, Attached r z u.val → EqvGen s u a) :
    Nat.card (Quotient (compSetoid r)) = Nat.card (Quotient (compSetoid s)) := by
  rw [card_comp_of_attached hs ha ha (fun u hu => Or.inl (hab u hu)),
    Setoid.adjoin_eq_self_of ((compSetoid s).refl' a)]

end Attached

end Deletion

end FourColor

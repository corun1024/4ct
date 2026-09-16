import FourColor.Walkup

/-!
# The Euler formula for hypermaps

The two sides of the hypermap Euler formula differ by an even number, so the
genus is exact: `EulerLhs = 2 * genus + EulerRhs`, and in particular
`EulerRhs ≤ EulerLhs`.

The proof is an induction on the number of darts through the Walkup
construction: deleting a dart preserves exactness (`evenGenus_walkupE`), and
the empty hypermap is exact because every count is zero.
-/

namespace FourColor

namespace Hypermap

universe u

/-- The Euler formula is exact for every hypermap with at most `n` darts. -/
private theorem evenGenus_of_card_le : ∀ (n : ℕ) {D : Type u} [Fintype D]
    (G : Hypermap D), Fintype.card D ≤ n → G.EvenGenus := by
  intro n
  induction n with
  | zero =>
    intro D _ G hn
    have hD : IsEmpty D := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hn)
    have hq : ∀ s : Setoid D, Nat.card (Quotient s) = 0 := fun s => by
      have : IsEmpty (Quotient s) :=
        ⟨fun q => Quotient.inductionOn q fun x => isEmptyElim x⟩
      exact Nat.card_of_isEmpty
    simp only [EvenGenus, genus, EulerLhs, EulerRhs, compCount, cycleCount, hq,
      Nat.card_of_isEmpty]
  | succ n ih =>
    intro D _ G hn
    classical
    rcases isEmpty_or_nonempty D with hD | hne
    · have hq : ∀ s : Setoid D, Nat.card (Quotient s) = 0 := fun s => by
        have : IsEmpty (Quotient s) :=
          ⟨fun q => Quotient.inductionOn q fun x => isEmptyElim x⟩
        exact Nat.card_of_isEmpty
      simp only [EvenGenus, genus, EulerLhs, EulerRhs, compCount, cycleCount, hq,
        Nat.card_of_isEmpty]
    · obtain ⟨z⟩ := hne
      refine evenGenus_walkupE G z (ih (G.walkupE z) ?_)
      have hcard := card_walkup G z
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
      omega

/-- The Euler formula: the genus of a hypermap is exact. -/
theorem evenGenus {D : Type u} [Fintype D] (G : Hypermap D) :
    G.EvenGenus :=
  evenGenus_of_card_le (Fintype.card D) G le_rfl

/-- The Euler inequality. -/
theorem eulerRhs_le_eulerLhs {D : Type u} [Fintype D] (G : Hypermap D) :
    G.EulerRhs ≤ G.EulerLhs := by
  have h := G.evenGenus
  simp only [EvenGenus] at h
  omega

/-- The genus, with no truncated subtraction. -/
theorem two_mul_genus {D : Type u} [Fintype D] (G : Hypermap D) :
    2 * G.genus = G.EulerLhs - G.EulerRhs := by
  have h := G.evenGenus
  simp only [EvenGenus] at h
  omega

end Hypermap

end FourColor

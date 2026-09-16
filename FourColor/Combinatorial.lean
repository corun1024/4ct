import FourColor.Cube
import FourColor.Coloring
import FourColor.Finitize

/-!
# The combinatorial Four Colour Theorem, from unavoidability

The unavoidability half of the proof says that no minimal counter-example
exists.  This file draws the consequence: every planar bridgeless hypermap is
four-colourable.  Two steps do it — pass to the cube construction, which is
plain and cubic of the same genus, and then induct on the number of darts,
since a smallest counter-example would be a minimal one.

## Main results

* `Hypermap.fourColorable_of_no_minimalCounterExample` — the combinatorial
  theorem, granted unavoidability.
* `fourColorTheorem_of` — the whole theorem, granted unavoidability and the
  discretisation of a finite simple map.
-/

namespace FourColor

namespace Hypermap

universe u

variable (h : ∀ {E : Type u} [Finite E] (H : Hypermap E), ¬ H.MinimalCounterExample)

include h in
/-- With no minimal counter-example, every planar bridgeless plain precubic map
with at most `n` darts is four-colourable. -/
private theorem colorable_of_card_le : ∀ (n : ℕ) {E : Type u} [Finite E] (H : Hypermap E),
    Nat.card E ≤ n → H.PlanarBridgelessPlainPrecubic → H.FourColorable := by
  intro n
  induction n with
  | zero =>
    intro E _ H hcard _
    have hE : IsEmpty E := by
      rw [Nat.le_zero, Nat.card_eq_zero] at hcard
      rcases hcard with hc | hc
      · exact hc
      · exact absurd hc (by rw [not_infinite_iff_finite]; infer_instance)
    exact ⟨fun _ => Color.c0, ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩⟩
  | succ n ih =>
    intro E _ H hcard hgeo
    by_contra hnc
    refine h H ⟨hgeo, hnc, ?_⟩
    intro E' _ H' hgeo' hlt
    exact ih H' (by omega) hgeo'

include h in
/-- The combinatorial Four Colour Theorem, granted unavoidability: a planar
bridgeless hypermap is four-colourable. -/
theorem fourColorable_of_no_minimalCounterExample {D : Type u} [Finite D]
    (G : Hypermap D) (hG : G.PlanarBridgeless) : G.FourColorable := by
  refine FourColorable.of_cube G ?_
  have hgeo : (G.cube).PlanarBridgelessPlainPrecubic :=
    ⟨⟨⟨(planar_cube G).mpr hG.planar, (bridgeless_cube G).mpr hG.bridgeless⟩, plain_cube G⟩,
      (cubic_cube G).precubic⟩
  exact colorable_of_card_le h _ _ le_rfl hgeo

end Hypermap

/-! ### The theorem, from its two remaining inputs

The Four Colour Theorem follows from two things this development does not yet
supply: **unavoidability** (no minimal counter-example exists, which the
presentation scripts establish) and the **discretisation** of a finite simple
map into a planar bridgeless hypermap (`discretize.v`, which needs
`gridmap.v`).  Everything between them is proved: the cube reduction and the
induction on darts here, and compactness in `FourColor/Finitize.lean`.
-/

/-- The Four Colour Theorem, granted unavoidability and discretisation. -/
theorem fourColorTheorem_of
    (unavoidability : ∀ {E : Type} [Finite E] (H : Hypermap E),
      ¬ H.MinimalCounterExample)
    (discretize : ∀ m : PlaneMap, FiniteSimpleMap m →
      ∃ (E : Type) (_ : Finite E) (G : Hypermap E),
        G.PlanarBridgeless ∧ (G.FourColorable → ColorableWith 4 m)) :
    FourColorTheorem := by
  refine fourColorTheorem_of_finite fun m hm => ?_
  obtain ⟨E, _, G, hG, hcol⟩ := discretize m hm
  exact hcol (Hypermap.fourColorable_of_no_minimalCounterExample unavoidability G hG)

end FourColor

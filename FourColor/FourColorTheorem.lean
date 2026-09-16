import FourColor.Combinatorial
import FourColor.Discretize

/-!
# The Four Colour Theorem, modulo unavoidability

`FourColor.Combinatorial` reduces the theorem to two statements: that a
minimal counter-example has no unavoidable configuration, and that a finite
simple map of the plane can be discretized to a hypermap.  The second is
`FourColor.discretize`, proved in `FourColor.Discretize`; this file discharges
it, leaving the first as the only hypothesis.
-/

namespace FourColor

/-- The Four Colour Theorem, assuming only that no hypermap is a minimal
counter-example — the unavoidability half of the proof. -/
theorem fourColorTheorem_of_unavoidability
    (unavoidability : ∀ {E : Type} [Finite E] (H : Hypermap E), ¬ H.MinimalCounterExample) :
    FourColorTheorem :=
  fourColorTheorem_of unavoidability discretize

end FourColor

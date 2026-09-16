import FourColor.FourColorTheorem
import FourColor.Unavoidability

/-!
# The Four Colour Theorem

Every statement of the development, assembled.  What is left are the two
computations the proof rests on, exactly as in the reference: that each of the
633 configurations is reducible, and the seven presentation scripts that make
the hub arities unavoidable.
-/

namespace FourColor

/-- **The Four Colour Theorem**, granted the two computations: that every
configuration of the database is reducible, and that each of the seven hub
arities is excluded by its presentation. -/
theorem fourColorTheorem_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e10 : ExcludedArity (RedpartSound theRedpart) 10)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11) :
    FourColorTheorem :=
  fourColorTheorem_of_unavoidability fun H =>
    Hypermap.not_minimalCounterExample (G := H) (redpartSound_theRedpart hred)
      e5 e6 e7 e8 e9 e10 e11

end FourColor

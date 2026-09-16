import FourColor.Main
import FourColor.Present5
import FourColor.Present6
import FourColor.Present7
import FourColor.Present8
import FourColor.Present9
import FourColor.Present10
import FourColor.Present11
import FourColor.Reduce.All

/-!
# The four colour theorem

`Main.lean` proves the theorem from eight computational facts: that every one of
the 633 configurations is reducible, and that each of the seven hub arities five
to eleven is excluded by its presentation.  This file discharges all eight and
states the theorem outright.

Nothing here is mathematics.  Each hypothesis is supplied by a module whose
content is a kernel computation:

* `reducible_all` chains the per-configuration reducibility certificates;
* `exclude5` … `exclude11` are the seven presentation scripts.

The reducibility side arrives as `reducible_all : ReducibleInRange 0 633 theConfigs`
from `FourColor.Reduce.All`; `theConfigs_length` turns that into `Reducibility`.
-/

namespace FourColor

/-- The number of configurations, evaluated once so that the range of
`reducible_all` can be matched against `theConfigs.length` without unfolding
the list of configurations. -/
theorem theConfigs_length : theConfigs.length = 633 := by decide +kernel

/-- Every configuration is reducible. -/
theorem reducibility : Reducibility := by
  unfold Reducibility
  rw [theConfigs_length]
  exact reducible_all

/-- **The four colour theorem.**  Every planar map can be four-coloured. -/
theorem fourColorTheorem : FourColorTheorem :=
  fourColorTheorem_of_checks reducibility
    exclude5 exclude6 exclude7 exclude8 exclude9 exclude10 exclude11

end FourColor

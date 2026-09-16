import FourColor.Present8Hub4

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 5 of the arity 8 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5171 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5159r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h8_5168 hred _
  intro _
  exact h8_5170 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5172 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5152r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h8_5165 hred _
  intro _
  exact h8_5171 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5173 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5042l := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact h8_5158 hred _
  intro _
  exact h8_5172 hred _

end FourColor

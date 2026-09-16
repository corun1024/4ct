import FourColor.Present10Hub1

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 2 of the arity 10 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_312 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_268r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_309 hred _
  intro _
  exact h10_311 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_313 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_267l := by
  refine succeed_by_split .hat 9 8 true (by decide +kernel) ?_ ?_
  · exact h10_306 hred _
  intro _
  exact h10_312 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_316 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_314l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_315

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_319 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_317l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_318

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_321 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_317r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_320

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_322 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_314r := by
  refine succeed_by_split .hat 9 5 true (by decide +kernel) ?_ ?_
  · exact h10_319 hred _
  intro _
  exact h10_321 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_323 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_267r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact h10_316 hred _
  intro _
  exact h10_322 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_324 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_256l := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact h10_313 hred _
  intro _
  exact h10_323 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_399 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_397l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_398

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_403 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_401l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_405 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_401r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_404

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_406 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_400l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_403 hred _
  intro _
  exact h10_405 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_408 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_400r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_407

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_409 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_397r := by
  refine succeed_by_split .spoke 9 7 true (by decide +kernel) ?_ ?_
  · exact h10_406 hred _
  intro _
  exact h10_408 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_410 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_369l := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact h10_399 hred _
  intro _
  exact h10_409 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_497 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_495l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_496

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_500 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_498l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_499

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_502 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_498r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 9 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_501

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_503 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_495r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h10_500 hred _
  intro _
  exact h10_502 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_504 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_466l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_497 hred _
  intro _
  exact h10_503 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_527 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_525l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_526

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_530 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_528l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_529

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_532 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_528r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.two 6 9 9 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_531

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_533 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_525r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact h10_530 hred _
  intro _
  exact h10_532 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_534 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_459l := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact h10_527 hred _
  intro _
  exact h10_533 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_653 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_651l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_652

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_655 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_651r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_654

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_656 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_633l := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact h10_653 hred _
  intro _
  exact h10_655 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_827 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_825l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_826

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_830 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_828l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_829

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_832 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_828r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_831

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_833 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_825r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h10_830 hred _
  intro _
  exact h10_832 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_834 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_824r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h10_827 hred _
  intro _
  exact h10_833 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_956 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_954l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_955

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_960 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_958l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_959

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_962 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_958r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_961

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_963 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_957l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h10_960 hred _
  intro _
  exact h10_962 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_965 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_957r := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_964

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_966 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_954r := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact h10_963 hred _
  intro _
  exact h10_965 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h10_967 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_953r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h10_956 hred _
  intro _
  exact h10_966 hred _

end FourColor

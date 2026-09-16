import FourColor.Present8Hub3

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 4 of the arity 8 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2597 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2593r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2596

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2598 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2561l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h8_2595 hred _
  intro _
  exact h8_2597 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2601 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2599l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2600

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2603 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2599r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_2604 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_2560l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h8_2601 hred _
  intro _
  exact h8_2603 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3348 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3346l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3347

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3350 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3346r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3349

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3351 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3320l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h8_3348 hred _
  intro _
  exact h8_3350 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3493 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3491l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3492

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3495 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3491r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3494

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3496 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3435l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h8_3493 hred _
  intro _
  exact h8_3495 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3499 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3497l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3498

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3501 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3497r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3500

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_3502 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_3434l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h8_3499 hred _
  intro _
  exact h8_3501 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4544 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4542l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4543

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4546 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4542r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4545

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4547 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4519l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h8_4544 hred _
  intro _
  exact h8_4546 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4585 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4583l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4584

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4587 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4583r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4586

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4588 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4548l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h8_4585 hred _
  intro _
  exact h8_4587 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4604 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4602l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4603

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4606 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4602r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4605

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4607 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4515l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact h8_4604 hred _
  intro _
  exact h8_4606 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4610 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4608l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4609

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4612 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4608r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4611

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_4613 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4514l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact h8_4610 hred _
  intro _
  exact h8_4612 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5001 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4999l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5003 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4999r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5002

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5004 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4998r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h8_5001 hred _
  intro _
  exact h8_5003 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5009 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5007l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5008

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5011 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5007r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5010

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5012 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_4997l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h8_5009 hred _
  intro _
  exact h8_5011 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5155 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5153l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5154

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5157 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5153r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5156

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5158 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5152l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h8_5155 hred _
  intro _
  exact h8_5157 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5162 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5160l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5161

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5164 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5160r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5163

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5165 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5159l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact h8_5162 hred _
  intro _
  exact h8_5164 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5168 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5166l := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h8_5170 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p8_5166r := by
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5169

end FourColor

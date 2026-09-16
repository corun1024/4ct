import FourColor.Present9Step1
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 2 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step643 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_635r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 1 8 7 <|
       Hubcap.two 2 4 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_642
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step641 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step645 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_633r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_644
  intro _
  exact s9_step643 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step652 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_633 p9_648r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_651
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_650

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step654 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_633 p9_646r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 8 7 <|
       Hubcap.two 2 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_653
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step652 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step656 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_633 p9_633l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_655
  intro _
  exact s9_step654 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step658 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_631r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_657
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact s9_step656 hred L1_1
  intro _
  exact s9_step645 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step660 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_630r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_659
  intro _
  exact s9_step658 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step662 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_629r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_661
  intro _
  exact s9_step660 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step664 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_628r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_663
  intro _
  exact s9_step662 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step666 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_561l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_665
  intro _
  exact s9_step664 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step667 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_560r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s9_step666 hred L1_1
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_627
  intro _
  exact s9_step626 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step669 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_559r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 0 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_668
  intro _
  exact s9_step667 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step671 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_558r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_670
  intro _
  exact s9_step669 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step673 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_557r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_672
  intro _
  exact s9_step671 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step675 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_343l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_674
  intro _
  exact s9_step673 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step676 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_318 p9_342r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s9_step675 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 3 8 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 2 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_556
  intro _
  exact s9_step555 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step694 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_318 p9_339r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_693
  intro _
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact h9_692 hred _
  intro _
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact h9_686 hred _
  intro _
  exact s9_step676 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step731 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709)
    (L3_2 : Successful q9_715) :
    SucceedsIn q9_317 p9_727r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 8 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_730
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 4 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_729

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step733 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709)
    (L3_2 : Successful q9_715) :
    SucceedsIn q9_317 p9_725r := by
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 5 6 <|
       Hubcap.two 2 6 7 <|
       Hubcap.two 3 7 7 <|
       Hubcap.two 4 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_732
  intro _
  exact s9_step731 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step734 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709)
    (L3_2 : Successful q9_715) :
    SucceedsIn q9_317 p9_721r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step733 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step735 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709)
    (L3_2 : Successful q9_715) :
    SucceedsIn q9_317 p9_717r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step734 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step751 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_747r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_750
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_749

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step753 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_745r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 5 7 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_752
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step751 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step755 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_743r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_754
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step753 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step757 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_741r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_756
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step755 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step759 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_739r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_758
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step757 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step761 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_737r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_760
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step759 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step763 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_715 p9_715l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_762
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step761 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step764 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_317 p9_713r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step763 hred L1_1 L3_1
  intro L3_2
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step735 hred L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step765 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_709) :
    SucceedsIn q9_317 p9_710r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step764 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step772 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_709 p9_768r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_771
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_770

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step774 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_709 p9_767r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_773
  intro _
  exact s9_step772 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step777 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_709 p9_709l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_776
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_775
  intro _
  exact s9_step774 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step779 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_707r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 0 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_778
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact s9_step777 hred L1_1
  intro L3_1
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step765 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step781 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_706r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_780
  intro _
  exact s9_step779 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step783 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_705r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_782
  intro _
  exact s9_step781 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step785 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_704r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_784
  intro _
  exact s9_step783 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step787 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_703r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_786
  intro _
  exact s9_step785 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step789 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_317 p9_702r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_788
  intro _
  exact s9_step787 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step790 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_16 p9_316r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step789 hred L1_1
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
    · exact h9_700 hred _
    intro _
    exact s9_step694 hred L1_1
  intro L2_1
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step338 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step791 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_1 p9_15r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step790 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step314 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step810 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_806r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_809
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_808

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step812 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_805r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_811
  intro _
  exact s9_step810 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step814 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_804r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_813
  intro _
  exact s9_step812 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step816 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_803r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_815
  intro _
  exact s9_step814 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step818 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_802r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_817
  intro _
  exact s9_step816 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step820 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_801r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_819
  intro _
  exact s9_step818 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step822 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_800r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_821
  intro _
  exact s9_step820 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step824 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_799r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_823
  intro _
  exact s9_step822 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step826 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_798r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_825
  intro _
  exact s9_step824 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step859 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796)
    (L3_1 : Successful q9_848)
    (L3_2 : Successful q9_854) :
    SucceedsIn q9_798 p9_856r := by
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_858

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step863 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796)
    (L3_1 : Successful q9_848) :
    SucceedsIn q9_854 p9_854l := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_862
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_861

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step864 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796)
    (L3_1 : Successful q9_848) :
    SucceedsIn q9_798 p9_852r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s9_step863 hred L2_1 L2_2 L2_3 L3_1
  intro L3_2
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step859 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step866 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796)
    (L3_1 : Successful q9_848) :
    SucceedsIn q9_798 p9_851r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_865
  intro _
  exact s9_step864 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step868 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796)
    (L3_1 : Successful q9_848) :
    SucceedsIn q9_798 p9_849r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_867
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step866 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step879 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_848 p9_875r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_878
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_877

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step881 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_848 p9_873r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_880
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step879 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step883 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_848 p9_870r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_882
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step881 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step884 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_847r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step883 hred L2_1 L2_2 L2_3
  intro L3_1
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step868 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step886 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_845r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_885
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step884 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step888 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_843r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_887
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step886 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step890 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_841r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_889
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step888 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step892 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_840r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_891
  intro _
  exact s9_step890 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step894 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_839r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_893
  intro _
  exact s9_step892 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step896 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_838r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_895
  intro _
  exact s9_step894 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step898 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_836r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_897
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step896 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step900 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_834r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_899
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step898 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step902 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_833r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_901
  intro _
  exact s9_step900 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step904 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_832r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_903
  intro _
  exact s9_step902 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step907 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_830r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_906
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_905
  intro _
  exact s9_step904 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step909 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_829r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_908
  intro _
  exact s9_step907 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step911 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_828r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_910
  intro _
  exact s9_step909 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step913 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_798 p9_827r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_912
  intro _
  exact s9_step911 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step915 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L2_3 : Successful q9_796) :
    SucceedsIn q9_14 p9_797r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap9 hred
        (Hubcap.one 3 4 <|
         Hubcap.one 4 4 <|
         Hubcap.one 7 4 <|
         Hubcap.two 0 8 7 <|
         Hubcap.two 1 2 5 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f9_914
    intro _
    exact s9_step913 hred L2_1 L2_2 L2_3
  intro _
  exact s9_step826 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step945 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_937 p9_941r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_944
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_943

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step947 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_937 p9_939r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_946
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step945 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step949 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_937 p9_937l := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_948
  intro _
  exact s9_step947 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step951 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_796 p9_935r := by
  refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_950
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s9_step949 hred L2_1 L2_2 L3_1 L3_2
  intro L3_3
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step953 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_796 p9_933r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_952
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step951 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step955 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_796 p9_931r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_954
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step953 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step957 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_796 p9_930r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_956
  intro _
  exact s9_step955 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step972 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_968r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_971
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_970

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step974 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_966r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_973
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step972 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step976 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_964r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_975
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step974 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step978 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_962r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_977
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step976 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step980 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_961r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_979
  intro _
  exact s9_step978 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step982 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_959r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_981
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step980 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step984 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_958r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_983
  intro _
  exact s9_step982 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step986 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_928 p9_928l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 7 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_985
  intro _
  exact s9_step984 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step997 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L3_2 : Successful q9_926) :
    SucceedsIn q9_796 p9_926r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact h9_996 hred _
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step986 hred L2_1 L2_2 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step957 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1003 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_926 p9_999r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1002
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1005 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_926 p9_998r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1004
  intro _
  exact s9_step1003 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1007 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_926 p9_926l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1006
  intro _
  exact s9_step1005 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1009 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_796 p9_924r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1008
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1007 hred L2_1 L2_2 L3_1
  intro L3_2
  exact s9_step997 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1011 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_796 p9_923r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1010
  intro _
  exact s9_step1009 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1030 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_922 p9_1027r := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1044 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1040r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1043
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1042

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1046 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1038r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1045
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1044 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1048 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1036r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1047
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1046 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1050 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1035r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1049
  intro _
  exact s9_step1048 hred L2_1 L2_2 L3_1 L4_1

end FourColor

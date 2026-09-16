import FourColor.Present7Step1
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 2 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step638 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_583r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 1 <|
         Hubcap.one 3 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 4 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_637
    intro _
    exact s7_step636 hred L0_1 L2_1
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step608 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step641 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_581r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_640
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 0 3 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_639
  intro _
  exact s7_step638 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step643 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_579r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_642
  intro _
  exact s7_step641 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step668 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_664r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_667
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_666

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step670 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_663r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_669
  intro _
  exact s7_step668 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step672 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_662r := by
  refine succeed_by_split .fan1 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_671
  intro _
  exact s7_step670 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step674 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_661r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_673
  intro _
  exact s7_step672 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step676 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_660r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_675
  intro _
  exact s7_step674 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step678 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_658r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_677
  intro _
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step676 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step681 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_656r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_680
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_679
  intro _
  exact s7_step678 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step684 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_654r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_683
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_682
  intro _
  exact s7_step681 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step687 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_652r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_686
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_685
  intro _
  exact s7_step684 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step689 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_651r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_688
  intro _
  exact s7_step687 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step699 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_650 p7_695r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_698
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_697

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step701 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_650 p7_694r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_700
  intro _
  exact s7_step699 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step703 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_650 p7_693r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_702
  intro _
  exact s7_step701 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step706 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_650 p7_691r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_705
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_704
  intro _
  exact s7_step703 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step707 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_649r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step706 hred L0_1 L2_1
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_690
  intro _
  exact s7_step689 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step721 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_717r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_720
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_719

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step723 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_716r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_722
  intro _
  exact s7_step721 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step725 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_715r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_724
  intro _
  exact s7_step723 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step728 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_713r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_727
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_726
  intro _
  exact s7_step725 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step731 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_711r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_730
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_729
  intro _
  exact s7_step728 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step733 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_709r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_732
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step731 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step735 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_649 p7_649l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_734
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step733 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step746 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_648 p7_742r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_745
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_744

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step749 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_648 p7_740r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_748
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_747
  intro _
  exact s7_step746 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step752 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_648 p7_738r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_751
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_750
  intro _
  exact s7_step749 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step755 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_648 p7_736r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_754
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_753
  intro _
  exact s7_step752 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step764 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_647 p7_760r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_763
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_762

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step767 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_647 p7_758r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_766
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_765
  intro _
  exact s7_step764 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step770 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_647 p7_756r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_769
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_768
  intro _
  exact s7_step767 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step771 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_646r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step770 hred L0_1 L2_1
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step755 hred L0_1 L2_1
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s7_step735 hred L0_1 L2_1
  intro _
  exact s7_step707 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step773 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_645r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_772
  intro _
  exact s7_step771 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step776 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_579 p7_579l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_775
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_774
  intro _
  exact s7_step773 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step793 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_789r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_792
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_791

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step795 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_787r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_794
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step793 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step798 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_785r := by
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 3 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_797
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_796
  intro _
  exact s7_step795 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step801 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_783r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_800
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_799
  intro _
  exact s7_step798 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step813 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_782 p7_809r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_812
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_811

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step815 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_782 p7_808r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_814
  intro _
  exact s7_step813 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step818 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_782 p7_806r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_817
  intro _
  refine succeed_by_split .fan1 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 5 2 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_816
  intro _
  exact s7_step815 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step821 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_782 p7_804r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_820
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 0 3 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_819
  intro _
  exact s7_step818 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step823 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_782 p7_802r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_822
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step821 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step825 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_781r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_824
    intro _
    exact s7_step823 hred L0_1 L2_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step801 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step828 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_779r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_827
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_826
  intro _
  exact s7_step825 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step830 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_578 p7_777r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_829
  intro _
  exact s7_step828 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step832 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_576r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_831
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step830 hred L0_1 L2_1
  intro _
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact s7_step776 hred L0_1 L2_1
  intro _
  exact s7_step643 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step835 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_574r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_834
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_833
  intro _
  exact s7_step832 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step837 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_36 p7_317r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_836
    intro _
    exact s7_step835 hred L0_1 L2_1
  intro L2_2
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step573 hred L0_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step568 hred L0_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step853 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_849r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_852
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_851

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step856 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_847r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_855
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_854
  intro _
  exact s7_step853 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step859 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_845r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_858
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_857
  intro _
  exact s7_step856 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step862 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_843r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_861
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_860
  intro _
  exact s7_step859 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step865 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_841r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_864
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_863
  intro _
  exact s7_step862 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step868 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_839r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_867
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_866
  intro _
  exact s7_step865 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step871 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_316 p7_316l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_870
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_869
  intro _
  exact s7_step868 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step873 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn q7_36 p7_36l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_872
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step871 hred L0_1
  intro L2_1
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step837 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step874 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn p7_0 p7_7r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step873 hred L0_1
    intro L1_1
    refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step314 hred L0_1 L1_1
  intro L0_2
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step35 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step875 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn p7_0 p7_4r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step874 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step876 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1) :
    SucceedsIn p7_0 p7_1r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step875 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step904 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889)
    (L1_8 : Successful q7_893) :
    SucceedsIn q7_896 p7_900r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_903
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_902

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step906 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889)
    (L1_8 : Successful q7_893) :
    SucceedsIn q7_896 p7_896l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_905
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step904 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step908 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889)
    (L1_8 : Successful q7_893) :
    SucceedsIn q7_1 p7_894r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_907
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step906 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8
  intro L1_9
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_9
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step916 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_893 p7_912r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_915
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_914

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step932 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_928r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_931
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_930

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step934 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_926r := by
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_933
  intro _
  exact s7_step932 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step937 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_924r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_936
  intro _
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_935
  intro _
  exact s7_step934 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step940 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_922r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_939
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_938
  intro _
  exact s7_step937 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step943 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_920r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_942
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_941
  intro _
  exact s7_step940 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step946 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_911 p7_918r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_945
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_944
  intro _
  exact s7_step943 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step948 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_893 p7_910r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 3 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_947
    intro _
    exact s7_step946 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_917
  intro _
  exact s7_step916 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step951 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_893 p7_893l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_950
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_949
  intro _
  exact s7_step948 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step953 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_1 p7_891r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_952
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step951 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7
  intro L1_8
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_8
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step908 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step955 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L1_7 : Successful q7_889) :
    SucceedsIn q7_1 p7_889r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_7
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_954
  intro _
  exact s7_step953 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step967 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957)
    (L2_2 : Successful q7_963) :
    SucceedsIn q7_889 p7_963r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_966

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step983 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_979r := by
  refine succeed_by_split .fan2 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_982
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_981

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step985 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_978r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_984
  intro _
  exact s7_step983 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step987 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_975r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_986
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step985 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step989 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_974r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_988
  intro _
  exact s7_step987 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step991 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_970r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_990
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step989 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step994 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_963 p7_968r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_993
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_992
  intro _
  exact s7_step991 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step996 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_889 p7_962r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 3 <|
         Hubcap.one 2 (-1) <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 3 <|
         Hubcap.two 3 5 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_995
    intro _
    exact s7_step994 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1
  intro L2_2
  exact s7_step967 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step998 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_889 p7_961r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_997
  intro _
  exact s7_step996 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1000 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_889 p7_960r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_999
  intro _
  exact s7_step998 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1008 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_959 p7_1004r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1007
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1006

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1011 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_959 p7_1002r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1010
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1009
  intro _
  exact s7_step1008 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1014 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_959 p7_959l := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1013
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1012
  intro _
  exact s7_step1011 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1021 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_958 p7_1017r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1020
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1019

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1023 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_958 p7_1015r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1022
  intro _
  exact s7_step1021 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1024 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887)
    (L2_1 : Successful q7_957) :
    SucceedsIn q7_889 p7_957r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step1023 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1014 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1000 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1034 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_957 p7_1030r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1033
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1032

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1040 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_1030 p7_1036r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1039
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1038

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1042 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_1030 p7_1035r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1041
  intro _
  exact s7_step1040 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1044 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_1030 p7_1030l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1043
  intro _
  exact s7_step1042 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1046 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_957 p7_1028r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1045
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1044 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro _
  exact s7_step1034 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1048 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_957 p7_1025r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1047
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1046 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1050 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885)
    (L1_6 : Successful q7_887) :
    SucceedsIn q7_889 p7_956r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 3 (-1) <|
         Hubcap.two 0 1 7 <|
         Hubcap.two 2 6 3 <|
         Hubcap.two 4 5 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1049
    intro _
    exact s7_step1048 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro L2_1
  exact s7_step1024 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1063 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1059r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1062
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1061

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1065 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1058r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1064
  intro _
  exact s7_step1063 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1067 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1056r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1066
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1065 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1072 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_1056 p7_1068r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1071
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1070

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1074 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1055r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 1 <|
         Hubcap.two 3 6 4 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1073
    intro _
    exact s7_step1072 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  exact s7_step1067 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1083 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_1054 p7_1079r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1082
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1081

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1086 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_1054 p7_1077r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1085
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1084
  intro _
  exact s7_step1083 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1089 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_1054 p7_1054l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1088
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1087
  intro _
  exact s7_step1086 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1090 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1053r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1089 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1075
  intro _
  exact s7_step1074 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1093 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_887 p7_1051r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1092
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1091
  intro _
  exact s7_step1090 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1095 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L1_5 : Successful q7_885) :
    SucceedsIn q7_1 p7_886r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1094
    intro _
    exact s7_step1093 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro L1_6
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step1050 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro L1_7
  exact s7_step955 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1120 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1116r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1119
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1118

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1122 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1114r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1121
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1120 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1132 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1114 p7_1128r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1131
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1130

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1134 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1114 p7_1126r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1133
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1132 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1136 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1114 p7_1125r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1135
  intro _
  exact s7_step1134 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1139 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1114 p7_1123r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1138
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1137
  intro _
  exact s7_step1136 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1141 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1114 p7_1114l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1140
  intro _
  exact s7_step1139 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1143 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1112r := by
  refine succeed_by_split .fan2 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1142
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1141 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step1122 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1146 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1110r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1145
  intro _
  refine succeed_by_split .fan1 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1144
  intro _
  exact s7_step1143 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1150 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1110 p7_1110l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1149
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1148

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1157 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1109 p7_1153r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1156
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1159 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1109 p7_1151r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1158
  intro _
  exact s7_step1157 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1161 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1109 p7_1109l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1160
  intro _
  exact s7_step1159 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1169 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1107 p7_1165r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1168
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1174 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1164 p7_1170r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1173
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1172

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1176 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1107 p7_1163r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 3 4 3 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1175
    intro _
    exact s7_step1174 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1169 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1184 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1162 p7_1180r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1183
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1182

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1190 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1179 p7_1186r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1189
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1188

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1192 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1179 p7_1179l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1191
  intro _
  exact s7_step1190 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1193 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1162 p7_1178r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1192 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1185
  intro _
  exact s7_step1184 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1195 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_1107 p7_1107l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 4 <|
         Hubcap.two 2 3 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_1194
    intro _
    exact s7_step1193 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1177
  intro _
  exact s7_step1176 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1196 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104) :
    SucceedsIn q7_885 p7_1106r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1195 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s7_step1161 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1150 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s7_step1146 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1207 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197)
    (L3_2 : Successful q7_1199) :
    SucceedsIn q7_1105 p7_1204r := by
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1206

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1209 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197)
    (L3_2 : Successful q7_1199) :
    SucceedsIn q7_1105 p7_1201r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 2 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1208
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1207 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1213 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197)
    (L3_2 : Successful q7_1199) :
    SucceedsIn q7_1200 p7_1200l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1212

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1214 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197)
    (L3_2 : Successful q7_1199) :
    SucceedsIn q7_1105 p7_1199r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s7_step1213 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1210
  intro _
  exact s7_step1209 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1222 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1199 p7_1218r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1221

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1230 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1216 p7_1226r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1229
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1228

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1232 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1216 p7_1224r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1231
  intro _
  exact s7_step1230 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1235 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1216 p7_1216l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1234
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1233
  intro _
  exact s7_step1232 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1237 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1199 p7_1199l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1236
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step1235 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step1222 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1246 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1198 p7_1242r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1245
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 2 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_1244

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1250 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1198 p7_1240r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact succeed_by_hubcap7 hred
      (Hubcap.one 2 1 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1249
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1247
  intro _
  exact s7_step1246 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step1253 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L1_4 : Successful q7_883)
    (L2_1 : Successful q7_1096)
    (L2_2 : Successful q7_1097)
    (L2_3 : Successful q7_1102)
    (L2_4 : Successful q7_1104)
    (L3_1 : Successful q7_1197) :
    SucceedsIn q7_1198 p7_1238r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 1 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1252
  intro _
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_1251
  intro _
  exact s7_step1250 hred L1_1 L1_2 L1_3 L1_4 L2_1 L2_2 L2_3 L2_4 L3_1

end FourColor

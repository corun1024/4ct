import FourColor.Present7Step9
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 10 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4608 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4600r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4607
  intro _
  exact s7_step4606 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4611 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4598r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4610
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4609
  intro _
  exact s7_step4608 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4613 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4596r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4612
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4611 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4616 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4594r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4615
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 6 3 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4614
  intro _
  exact s7_step4613 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4621 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4594 p7_4617r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4620
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4619

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4623 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4528l := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4622
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4621 hred L1_1
  intro _
  exact s7_step4616 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4639 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628)
    (L5_4 : Successful q7_4630)
    (L5_5 : Successful q7_4634) :
    SucceedsIn q7_4527 p7_4636r := by
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4638

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4645 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628)
    (L5_4 : Successful q7_4630) :
    SucceedsIn q7_4634 p7_4641r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4644
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4643

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4648 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628)
    (L5_4 : Successful q7_4630) :
    SucceedsIn q7_4634 p7_4634l := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4647
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4646
  intro _
  exact s7_step4645 hred L1_1 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4650 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628)
    (L5_4 : Successful q7_4630) :
    SucceedsIn q7_4527 p7_4632r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4649
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s7_step4648 hred L1_1 L5_1 L5_2 L5_3 L5_4
  intro L5_5
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4639 hred L1_1 L5_1 L5_2 L5_3 L5_4 L5_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4652 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628)
    (L5_4 : Successful q7_4630) :
    SucceedsIn q7_4527 p7_4630r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4651
  intro _
  exact s7_step4650 hred L1_1 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4659 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628) :
    SucceedsIn q7_4630 p7_4655r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4658
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4657

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4662 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628) :
    SucceedsIn q7_4630 p7_4653r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4661
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4660
  intro _
  exact s7_step4659 hred L1_1 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4664 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626)
    (L5_3 : Successful q7_4628) :
    SucceedsIn q7_4527 p7_4629r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.one 6 (-1) <|
         Hubcap.two 1 5 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4663
    intro _
    exact s7_step4662 hred L1_1 L5_1 L5_2 L5_3
  intro L5_4
  exact s7_step4652 hred L1_1 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4672 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4628 p7_4668r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4671
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4670

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4681 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4667 p7_4677r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4680
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4679

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4684 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4667 p7_4675r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4683
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4682
  intro _
  exact s7_step4681 hred L1_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4687 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4667 p7_4667l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4686
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4685
  intro _
  exact s7_step4684 hred L1_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4688 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4628 p7_4666r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s7_step4687 hred L1_1 L5_1 L5_2
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4673
  intro _
  exact s7_step4672 hred L1_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4691 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L5_2 : Successful q7_4626) :
    SucceedsIn q7_4628 p7_4628l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4690
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4689
  intro _
  exact s7_step4688 hred L1_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4704 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4626 p7_4700r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4703
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4702

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4707 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4626 p7_4698r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4706
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4705
  intro _
  exact s7_step4704 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4715 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4697 p7_4711r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4714
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4713

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4718 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4697 p7_4709r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4717
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4716
  intro _
  exact s7_step4715 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4720 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4626 p7_4696r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 1 <|
         Hubcap.one 6 0 <|
         Hubcap.two 1 3 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4719
    intro _
    exact s7_step4718 hred L1_1 L5_1
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4708
  intro _
  exact s7_step4707 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4733 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4729r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4732
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4731

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4735 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4728r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4734
  intro _
  exact s7_step4733 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4737 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4725r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4736
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan3 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4735 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4740 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4723r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4739
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4738
  intro _
  exact s7_step4737 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4743 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4721r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4742
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 6 0 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4741
  intro _
  exact s7_step4740 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4745 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4696 p7_4696l := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4744
  intro _
  exact s7_step4743 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4752 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4695 p7_4748r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4751
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4750

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4757 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4748 p7_4753r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4756
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4755

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4759 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4695 p7_4747r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 3 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4758
    intro _
    exact s7_step4757 hred L1_1 L5_1
  intro _
  exact s7_step4752 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4762 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4695 p7_4695l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4761
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4760
  intro _
  exact s7_step4759 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4774 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4770r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4773
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4772

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4776 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4769r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4775
  intro _
  exact s7_step4774 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4778 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4767r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4777
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4776 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4781 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4765r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4780
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4779
  intro _
  exact s7_step4778 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4787 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4765 p7_4783r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4786
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4785

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4790 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4765 p7_4765l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4789
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4788
  intro _
  exact s7_step4787 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4792 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4763r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4791
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4790 hred L1_1 L5_1
  intro _
  exact s7_step4781 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4803 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4763 p7_4799r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4802
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4801

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4806 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4763 p7_4797r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4805
  intro _
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4804
  intro _
  exact s7_step4803 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4809 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4763 p7_4795r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4808
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4807
  intro _
  exact s7_step4806 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4811 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4763 p7_4793r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4810
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4809 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4813 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4694 p7_4694l := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 4 2 <|
         Hubcap.one 6 0 <|
         Hubcap.two 3 5 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4812
    intro _
    exact s7_step4811 hred L1_1 L5_1
  intro _
  exact s7_step4792 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4829 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L7_1 : Successful q7_4817) :
    SucceedsIn q7_4693 p7_4825r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4828
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4827

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4832 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L7_1 : Successful q7_4817) :
    SucceedsIn q7_4693 p7_4823r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4831
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4830
  intro _
  exact s7_step4829 hred L1_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4835 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L7_1 : Successful q7_4817) :
    SucceedsIn q7_4693 p7_4821r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4834
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4833
  intro _
  exact s7_step4832 hred L1_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4838 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L7_1 : Successful q7_4817) :
    SucceedsIn q7_4693 p7_4819r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4837
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4836
  intro _
  exact s7_step4835 hred L1_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4840 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624)
    (L7_1 : Successful q7_4817) :
    SucceedsIn q7_4693 p7_4817r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L7_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4839
  intro _
  exact s7_step4838 hred L1_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4850 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4846r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4849
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4848

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4852 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4845r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4851
  intro _
  exact s7_step4850 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4854 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4844r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4853
  intro _
  exact s7_step4852 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4856 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4843r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4855
  intro _
  exact s7_step4854 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4858 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4842r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4857
  intro _
  exact s7_step4856 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4861 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4817 p7_4817l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4860
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4859
  intro _
  exact s7_step4858 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4863 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4693 p7_4815r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4862
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4861 hred L1_1 L5_1
  intro L7_1
  exact s7_step4840 hred L1_1 L5_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4866 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4693 p7_4693l := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4865
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4864
  intro _
  exact s7_step4863 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4867 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4626 p7_4692r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4866 hred L1_1 L5_1
  intro _
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact s7_step4813 hred L1_1 L5_1
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4762 hred L1_1 L5_1
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact s7_step4745 hred L1_1 L5_1
  intro _
  exact s7_step4720 hred L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4869 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L5_1 : Successful q7_4624) :
    SucceedsIn q7_4527 p7_4625r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4868
    intro _
    exact s7_step4867 hred L1_1 L5_1
  intro L5_2
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4691 hred L1_1 L5_1 L5_2
  intro L5_3
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step4664 hred L1_1 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4885 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4881r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4884
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4883

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4887 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4880r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4886
  intro _
  exact s7_step4885 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4889 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4879r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4888
  intro _
  exact s7_step4887 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4891 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4878r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4890
  intro _
  exact s7_step4889 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4893 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4877r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4892
  intro _
  exact s7_step4891 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4903 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4875 p7_4899r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4902
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4901

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4905 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4875 p7_4898r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4904
  intro _
  exact s7_step4903 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4907 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4875 p7_4896r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4906
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4905 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4909 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4875 p7_4895r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4908
  intro _
  exact s7_step4907 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4915 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4895 p7_4911r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4914
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4913

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4917 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4895 p7_4910r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4916
  intro _
  exact s7_step4915 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4919 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4895 p7_4895l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4918
  intro _
  exact s7_step4917 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4928 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4894 p7_4924r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4927
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4926

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4930 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4894 p7_4923r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4929
  intro _
  exact s7_step4928 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4932 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4894 p7_4921r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4931
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4930 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4934 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4894 p7_4920r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4933
  intro _
  exact s7_step4932 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4940 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4920 p7_4936r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4939
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4938

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4942 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4920 p7_4935r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4941
  intro _
  exact s7_step4940 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4944 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4920 p7_4920l := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4943
  intro _
  exact s7_step4942 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4945 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4874r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
      · exact s7_step4944 hred L1_1
      intro _
      exact s7_step4934 hred L1_1
    intro _
    refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact s7_step4919 hred L1_1
    intro _
    exact s7_step4909 hred L1_1
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4893 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4955 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4873 p7_4951r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4954
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4953

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4957 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4873 p7_4949r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4956
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4955 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4959 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4873 p7_4947r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4958
  intro _
  exact s7_step4957 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4961 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4873 p7_4873l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4960
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4959 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4968 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4871 p7_4964r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4967
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4966

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4970 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4871 p7_4962r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4969
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4968 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4972 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4624 p7_4870r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 4 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 0 <|
         Hubcap.two 2 3 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_4971
    intro _
    exact s7_step4970 hred L1_1
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s7_step4961 hred L1_1
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4945 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4973 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4517 p7_4517l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s7_step4972 hred L1_1
    intro L5_1
    refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 2 true L5_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step4869 hred L1_1 L5_1
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4623 hred L1_1
  intro _
  exact s7_step4592 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4974 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_879 p7_3437r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact s7_step4973 hred L1_1
    intro L3_1
    exact s7_step4526 hred L1_1 L3_1
  intro L2_1
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact s7_step4515 hred L1_1 L2_1
  intro _
  exact s7_step4106 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4975 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_1 p7_877r := by
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 2 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step4974 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3436 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5003 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_877 p7_4999r := by
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5002
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5006 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_877 p7_4997r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5005
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5004
  intro _
  exact s7_step5003 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5009 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_877 p7_4995r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5008
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5007
  intro _
  exact s7_step5006 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5012 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_877 p7_4993r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5011
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5010
  intro _
  exact s7_step5009 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5015 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_877 p7_4991r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5014
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5013
  intro _
  exact s7_step5012 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5021 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_4991 p7_5017r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5020
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5019

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5024 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L2_5 : Successful q7_4989) :
    SucceedsIn q7_4991 p7_4991l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5023
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5022
  intro _
  exact s7_step5021 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5034 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L3_1 : Successful q7_5027) :
    SucceedsIn q7_4989 p7_5030r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5033
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5032

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5037 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987)
    (L3_1 : Successful q7_5027) :
    SucceedsIn q7_4989 p7_5028r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5036
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5035
  intro _
  exact s7_step5034 hred L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5041 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987) :
    SucceedsIn q7_5027 p7_5027l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5040
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5039

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5043 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987) :
    SucceedsIn q7_4989 p7_5025r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5042
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5041 hred L2_1 L2_2 L2_3 L2_4
  intro L3_1
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5037 hred L2_1 L2_2 L2_3 L2_4 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5044 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L2_4 : Successful q7_4987) :
    SucceedsIn q7_877 p7_4988r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5043 hred L2_1 L2_2 L2_3 L2_4
  intro L2_5
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5024 hred L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step5015 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5059 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5055r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5058
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5057

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5061 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5054r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 4 6 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5060
  intro _
  exact s7_step5059 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5063 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5052r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5062
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5061 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5066 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5050r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5065
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 1 <|
       Hubcap.two 2 6 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5064
  intro _
  exact s7_step5063 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5068 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5048r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5067
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5066 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5071 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_5046r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5070
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5069
  intro _
  exact s7_step5068 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5074 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4987 p7_4987l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5073
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5072
  intro _
  exact s7_step5071 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5075 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_877 p7_4984r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5074 hred L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5044 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5091 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078)
    (L3_3 : Successful q7_5085) :
    SucceedsIn q7_4984 p7_5087r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5090
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5089

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5093 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078)
    (L3_3 : Successful q7_5085) :
    SucceedsIn q7_4984 p7_5085r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5092
  intro _
  exact s7_step5091 hred L2_1 L2_2 L2_3 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5102 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_5085 p7_5098r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5101
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5100

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5104 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_5085 p7_5094r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5103
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5102 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5106 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_4984 p7_5083r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5105
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5104 hred L2_1 L2_2 L2_3 L3_1 L3_2
  intro L3_3
  exact s7_step5093 hred L2_1 L2_2 L2_3 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5113 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_5082 p7_5109r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5112
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5111

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5115 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_5082 p7_5108r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5114
  intro _
  exact s7_step5113 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5117 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_5082 p7_5082l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5116
  intro _
  exact s7_step5115 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5118 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_4984 p7_5081r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5117 hred L2_1 L2_2 L2_3 L3_1 L3_2
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 4 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5107
  intro _
  exact s7_step5106 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5121 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L3_2 : Successful q7_5078) :
    SucceedsIn q7_4984 p7_5079r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5120
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5119
  intro _
  exact s7_step5118 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5137 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5133r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5136
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5140 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5131r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5139
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5138
  intro _
  exact s7_step5137 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5142 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5130r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5141
  intro _
  exact s7_step5140 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5145 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5128r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 2 4 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5144
  intro _
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.two 2 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5143
  intro _
  exact s7_step5142 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5147 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5126r := by
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5146
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5145 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5153 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5126 p7_5149r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5152
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5151

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5156 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5126 p7_5126l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5155
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5154
  intro _
  exact s7_step5153 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5158 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5078 p7_5124r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5157
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5156 hred L2_1 L2_2 L2_3 L3_1 L4_1
  intro _
  exact s7_step5147 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5165 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5124 p7_5161r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5164
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5163

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5167 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5124 p7_5160r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5166
  intro _
  exact s7_step5165 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5169 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076)
    (L4_1 : Successful q7_5123) :
    SucceedsIn q7_5124 p7_5124l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5168
  intro _
  exact s7_step5167 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5178 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076) :
    SucceedsIn q7_5123 p7_5174r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5177
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5180 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076) :
    SucceedsIn q7_5123 p7_5172r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5179
  intro _
  exact s7_step5178 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5183 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076) :
    SucceedsIn q7_5123 p7_5170r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5182
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5181
  intro _
  exact s7_step5180 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5184 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981)
    (L3_1 : Successful q7_5076) :
    SucceedsIn q7_5078 p7_5078l := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5183 hred L2_1 L2_2 L2_3 L3_1
  intro L4_1
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact s7_step5169 hred L2_1 L2_2 L2_3 L3_1 L4_1
  intro _
  exact s7_step5158 hred L2_1 L2_2 L2_3 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5194 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_5076 p7_5190r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5193
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5192

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5196 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_5076 p7_5188r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5195
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5194 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5199 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_5076 p7_5186r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5198
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5197
  intro _
  exact s7_step5196 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5202 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_5076 p7_5076l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5201
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5200
  intro _
  exact s7_step5199 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5203 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_4984 p7_4984l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5202 hred L2_1 L2_2 L2_3
  intro L3_1
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s7_step5184 hred L2_1 L2_2 L2_3 L3_1
  intro L3_2
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5121 hred L2_1 L2_2 L2_3 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5205 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L2_3 : Successful q7_4981) :
    SucceedsIn q7_877 p7_4982r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5204
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step5203 hred L2_1 L2_2 L2_3
  intro _
  exact s7_step5075 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5222 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5210 p7_5218r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5221
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5220

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5224 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5210 p7_5216r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5223
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5222 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5227 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5210 p7_5214r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5226
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5225
  intro _
  exact s7_step5224 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5229 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_5210 p7_5212r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5228
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5227 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5231 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206) :
    SucceedsIn q7_4981 p7_5209r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 4 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 5 6 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_5230
    intro _
    exact s7_step5229 hred L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5245 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206)
    (L4_1 : Successful q7_5234) :
    SucceedsIn q7_5237 p7_5241r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5244
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5243

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5247 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206)
    (L4_1 : Successful q7_5234) :
    SucceedsIn q7_5237 p7_5237l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5246
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5245 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5250 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206)
    (L4_1 : Successful q7_5234) :
    SucceedsIn q7_5236 p7_5236l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_5249

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step5251 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q7_4976)
    (L2_2 : Successful q7_4978)
    (L3_1 : Successful q7_5206)
    (L4_1 : Successful q7_5234) :
    SucceedsIn q7_5208 p7_5235r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step5250 hred L2_1 L2_2 L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5247 hred L2_1 L2_2 L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

end FourColor

import FourColor.Present8Step8
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 9 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4792 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4762 p8_4769r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4791
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step4790 hred L2_1
  intro L6_1
  exact s8_step4783 hred L2_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4798 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4769 p8_4794r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4797
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4796

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4800 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4769 p8_4769l := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4799
  intro _
  exact s8_step4798 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4801 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4713 p8_4761r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact s8_step4800 hred L2_1
    intro _
    exact s8_step4792 hred L2_1
  intro L5_1
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step4768 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4802 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4220 p8_4220l := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step4801 hred L2_1
  intro L4_1
  exact s8_step4759 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4822 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813)
    (L4_5 : Successful q8_4815) :
    SucceedsIn q8_4219 p8_4818r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4821
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4820

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4824 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813)
    (L4_5 : Successful q8_4815) :
    SucceedsIn q8_4219 p8_4817r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4823
  intro _
  exact s8_step4822 hred L2_1 L4_1 L4_2 L4_3 L4_4 L4_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4829 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813)
    (L4_5 : Successful q8_4815) :
    SucceedsIn q8_4817 p8_4825r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4828
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4827

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4831 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813)
    (L4_5 : Successful q8_4815) :
    SucceedsIn q8_4817 p8_4817l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4830
  intro _
  exact s8_step4829 hred L2_1 L4_1 L4_2 L4_3 L4_4 L4_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4837 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4815 p8_4833r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4836
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4835

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4844 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4832 p8_4840r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4843
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4842

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4846 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4832 p8_4839r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4845
  intro _
  exact s8_step4844 hred L2_1 L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4848 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4832 p8_4832l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4847
  intro _
  exact s8_step4846 hred L2_1 L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4849 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4815 p8_4815l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step4848 hred L2_1 L4_1 L4_2 L4_3 L4_4
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4838
  intro _
  exact s8_step4837 hred L2_1 L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4850 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810)
    (L4_4 : Successful q8_4813) :
    SucceedsIn q8_4219 p8_4813r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s8_step4849 hred L2_1 L4_1 L4_2 L4_3 L4_4
  intro L4_5
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact s8_step4831 hred L2_1 L4_1 L4_2 L4_3 L4_4 L4_5
  intro _
  exact s8_step4824 hred L2_1 L4_1 L4_2 L4_3 L4_4 L4_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4861 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4857r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4860
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4859

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4863 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4855r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4862
  intro _
  exact s8_step4861 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4865 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4854r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4864
  intro _
  exact s8_step4863 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4868 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4852r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4867
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4866
  intro _
  exact s8_step4865 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4870 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4851r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4869
  intro _
  exact s8_step4868 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4872 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4813 p8_4813l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4871
  intro _
  exact s8_step4870 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4878 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4812 p8_4874r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4877
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4876

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4880 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4812 p8_4873r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4879
  intro _
  exact s8_step4878 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4882 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808)
    (L4_3 : Successful q8_4810) :
    SucceedsIn q8_4812 p8_4812l := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4881
  intro _
  exact s8_step4880 hred L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4892 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4888r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4891
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4890

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4894 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4887r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4893
  intro _
  exact s8_step4892 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4896 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4885r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4895
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step4894 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4898 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4884r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4897
  intro _
  exact s8_step4896 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4900 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4883r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4899
  intro _
  exact s8_step4898 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4902 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4810 p8_4810l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4901
  intro _
  exact s8_step4900 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4903 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806)
    (L4_2 : Successful q8_4808) :
    SucceedsIn q8_4219 p8_4809r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s8_step4902 hred L2_1 L4_1 L4_2
  intro L4_3
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s8_step4882 hred L2_1 L4_1 L4_2 L4_3
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step4872 hred L2_1 L4_1 L4_2 L4_3
  intro L4_4
  exact s8_step4850 hred L2_1 L4_1 L4_2 L4_3 L4_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4918 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4914r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4917
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4916

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4920 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4913r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4919
  intro _
  exact s8_step4918 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4922 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4911r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4921
  intro _
  exact s8_step4920 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4924 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4910r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4923
  intro _
  exact s8_step4922 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4927 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4908r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4926
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4925
  intro _
  exact s8_step4924 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4929 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4907r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4928
  intro _
  exact s8_step4927 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4931 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4906r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4930
  intro _
  exact s8_step4929 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4933 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4808 p8_4905r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4932
  intro _
  exact s8_step4931 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4934 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L4_1 : Successful q8_4806) :
    SucceedsIn q8_4219 p8_4807r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step4933 hred L2_1 L4_1
  intro L4_2
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step4903 hred L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4947 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4806 p8_4943r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4946
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4945

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4952 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4941 p8_4948r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4951
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4950

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4954 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4941 p8_4941l := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4953
  intro _
  exact s8_step4952 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4955 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4806 p8_4939r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step4954 hred L2_1
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step4947 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4965 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4961r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4964
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4963

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4967 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4960r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4966
  intro _
  exact s8_step4965 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4969 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4959r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4968
  intro _
  exact s8_step4967 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4971 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4958r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4970
  intro _
  exact s8_step4969 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4973 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4957r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4972
  intro _
  exact s8_step4971 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4975 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4956r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4974
  intro _
  exact s8_step4973 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4977 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4939 p8_4939l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4976
  intro _
  exact s8_step4975 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4979 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4806 p8_4937r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4978
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step4977 hred L2_1
  intro _
  exact s8_step4955 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4981 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4806 p8_4936r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4980
  intro _
  exact s8_step4979 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4983 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4806 p8_4935r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_4982
  intro _
  exact s8_step4981 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4993 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L5_1 : Successful q8_4984)
    (L5_2 : Successful q8_4986) :
    SucceedsIn q8_4805 p8_4990r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_4992

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step4994 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L5_1 : Successful q8_4984)
    (L5_2 : Successful q8_4986) :
    SucceedsIn q8_4805 p8_4986r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step4993 hred L2_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5006 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L5_1 : Successful q8_4984) :
    SucceedsIn q8_4986 p8_4997r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5005
  intro _
  exact h8_5004 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5014 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L5_1 : Successful q8_4984) :
    SucceedsIn q8_4986 p8_4995r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5013
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact h8_5012 hred _
  intro _
  exact s8_step5006 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5016 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L5_1 : Successful q8_4984) :
    SucceedsIn q8_4805 p8_4985r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 1 2 <|
         Hubcap.one 3 3 <|
         Hubcap.one 4 3 <|
         Hubcap.one 5 0 <|
         Hubcap.two 0 6 5 <|
         Hubcap.two 2 7 7 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_5015
    intro _
    exact s8_step5014 hred L2_1 L5_1
  intro L5_2
  exact s8_step4994 hred L2_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5026 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4984 p8_5022r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5025
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5024

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5028 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4984 p8_5021r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5027
  intro _
  exact s8_step5026 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5030 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4984 p8_5020r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5029
  intro _
  exact s8_step5028 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5032 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4984 p8_5018r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5031
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5030 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5033 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4805 p8_4805l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5032 hred L2_1
  intro L5_1
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5016 hred L2_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5034 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_4219 p8_4804r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact s8_step5033 hred L2_1
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step4983 hred L2_1
  intro L4_1
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step4934 hred L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5035 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_2737 p8_2737l := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5034 hred L2_1
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact s8_step4802 hred L2_1
  intro _
  exact s8_step4711 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5036 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735) :
    SucceedsIn q8_116 p8_2735r := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact s8_step5035 hred L2_1
  intro L2_2
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact s8_step4218 hred L2_1 L2_2
  intro L2_3
  exact s8_step3135 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5054 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045)
    (L3_5 : Successful q8_5047) :
    SucceedsIn q8_2735 p8_5050r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5053
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5052

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5057 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045)
    (L3_5 : Successful q8_5047) :
    SucceedsIn q8_2735 p8_5048r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5056
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5055
  intro _
  exact s8_step5054 hred L3_1 L3_2 L3_3 L3_4 L3_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5071 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5067r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5070
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5069

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5073 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5066r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5072
  intro _
  exact s8_step5071 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5075 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5065r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5074
  intro _
  exact s8_step5073 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5077 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5064r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5076
  intro _
  exact s8_step5075 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5079 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5063r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5078
  intro _
  exact s8_step5077 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5081 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5062r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 2 4 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5080
  intro _
  exact s8_step5079 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5087 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5062 p8_5083r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5086
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5085

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5089 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5062 p8_5082r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5088
  intro _
  exact s8_step5087 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5091 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5062 p8_5062l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5090
  intro _
  exact s8_step5089 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5093 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5060r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5092
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step5091 hred L3_1 L3_2 L3_3 L3_4
  intro _
  exact s8_step5081 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5095 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_5047 p8_5059r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5094
  intro _
  exact s8_step5093 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5096 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L3_4 : Successful q8_5045) :
    SucceedsIn q8_2735 p8_5046r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5095 hred L3_1 L3_2 L3_3 L3_4
  intro L3_5
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5057 hred L3_1 L3_2 L3_3 L3_4 L3_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5109 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L4_1 : Successful q8_5100) :
    SucceedsIn q8_5045 p8_5105r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5108
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5107

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5111 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043)
    (L4_1 : Successful q8_5100) :
    SucceedsIn q8_5045 p8_5103r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5110
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5109 hred L3_1 L3_2 L3_3 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5124 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5120r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5123
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5122

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5126 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5118r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5125
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5124 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5128 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5116r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5127
  intro _
  exact s8_step5126 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5130 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5115r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5129
  intro _
  exact s8_step5128 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5132 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5113r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5131
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5130 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5134 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5100 p8_5100l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5133
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5132 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5135 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5045 p8_5099r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact s8_step5134 hred L3_1 L3_2 L3_3
  intro L4_1
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5111 hred L3_1 L3_2 L3_3 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5138 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_5045 p8_5097r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5137
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5136
  intro _
  exact s8_step5135 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5139 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L3_3 : Successful q8_5043) :
    SucceedsIn q8_2735 p8_5043r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5138 hred L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5096 hred L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5146 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5043 p8_5142r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5145
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5144

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5149 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5043 p8_5140r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5148
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5147
  intro _
  exact s8_step5146 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5151 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_2735 p8_5042r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 1 2 <|
         Hubcap.one 5 4 <|
         Hubcap.one 6 5 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 4 7 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_5150
    intro _
    exact s8_step5149 hred L3_1 L3_2
  intro L3_3
  exact s8_step5139 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5185 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L4_1 : Successful q8_5174) :
    SucceedsIn q8_5041 p8_5181r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5184
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5183

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5187 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L4_1 : Successful q8_5174) :
    SucceedsIn q8_5041 p8_5180r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5186
  intro _
  exact s8_step5185 hred L3_1 L3_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5189 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L4_1 : Successful q8_5174) :
    SucceedsIn q8_5041 p8_5179r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5188
  intro _
  exact s8_step5187 hred L3_1 L3_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5192 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L4_1 : Successful q8_5174) :
    SucceedsIn q8_5041 p8_5177r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 5 6 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5191
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5190
  intro _
  exact s8_step5189 hred L3_1 L3_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5195 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039)
    (L4_1 : Successful q8_5174) :
    SucceedsIn q8_5041 p8_5175r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 5 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5194
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5193
  intro _
  exact s8_step5192 hred L3_1 L3_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5209 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5205r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5208
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5207

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5211 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5203r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5210
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5209 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5213 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5202r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5212
  intro _
  exact s8_step5211 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5215 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5201r := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5214
  intro _
  exact s8_step5213 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5222 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5201 p8_5218r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5221
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5220

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5224 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5201 p8_5216r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5223
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5222 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5226 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5201 p8_5201l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5225
  intro _
  exact s8_step5224 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5234 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5200 p8_5230r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5233
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5232

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5236 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5200 p8_5229r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5235
  intro _
  exact s8_step5234 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5238 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5200 p8_5228r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5237
  intro _
  exact s8_step5236 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5240 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5200 p8_5227r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5239
  intro _
  exact s8_step5238 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5246 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5199 p8_5242r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5245
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5244

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5247 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5198r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5246 hred L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5240 hred L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step5226 hred L3_1 L3_2
  intro _
  exact s8_step5215 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5249 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_5174 p8_5196r := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5248
  intro _
  exact s8_step5247 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5250 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037)
    (L3_2 : Successful q8_5039) :
    SucceedsIn q8_2735 p8_5040r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s8_step5249 hred L3_1 L3_2
    intro L4_1
    refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s8_step5195 hred L3_1 L3_2 L4_1
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact h8_5173 hred _
  intro _
  exact s8_step5151 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5265 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5261r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5264
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5263

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5267 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5260r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5266
  intro _
  exact s8_step5265 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5272 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5259 p8_5268r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5271
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5270

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5274 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5259 p8_5259l := by
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5273
  intro _
  exact s8_step5272 hred L3_1

end FourColor

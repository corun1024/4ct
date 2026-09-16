import FourColor.Present5Chk1
import FourColor.TheQuizTree

/-!
Translated from `present5.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 5 presentation

A chunk of the case analysis of `present5.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step7 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q5_1) :
    SucceedsIn p5_0 p5_3r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap5 hred
    (Hubcap.two 0 1 (-4) <|
     Hubcap.two 2 3 (-4) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f5_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step18 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q5_8)
    (L1_2 : Successful q5_10) :
    SucceedsIn q5_12 p5_12l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap5 hred
      (Hubcap.two 0 1 (-3) <|
       Hubcap.two 2 3 (-4) <|
       Hubcap.one 4 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f5_17
  intro _
  exact succeed_by_hubcap5 hred
    (Hubcap.two 0 1 (-3) <|
     Hubcap.two 2 3 (-5) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f5_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step19 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q5_8)
    (L1_2 : Successful q5_10) :
    SucceedsIn q5_1 p5_11r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s5_step18 hred L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap5 hred
    (Hubcap.two 0 1 (-2) <|
     Hubcap.two 2 3 (-6) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f5_14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step27 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q5_8) :
    SucceedsIn q5_10 p5_21r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact succeed_by_hubcap5 hred
      (Hubcap.two 0 1 (-4) <|
       Hubcap.two 2 3 (-2) <|
       Hubcap.one 4 (-4) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f5_26
  intro L2_1
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap5 hred
    (Hubcap.two 0 1 (-4) <|
     Hubcap.two 2 3 (-3) <|
     Hubcap.one 4 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f5_24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step28 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q5_8) :
    SucceedsIn q5_1 p5_9r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 2 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s5_step27 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s5_step19 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step34 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q5_29) :
    SucceedsIn q5_8 p5_30r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap5 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 3 (-6) <|
       Hubcap.one 4 (-4) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f5_33
  intro _
  exact succeed_by_hubcap5 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 3 (-5) <|
     Hubcap.one 4 (-5) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f5_32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step41 (hred : RedpartSound theRedpart) :
    SucceedsIn q5_29 p5_36r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap5 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 3 (-6) <|
       Hubcap.one 4 (-4) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f5_40
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap5 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 3 (-7) <|
       Hubcap.one 4 (-3) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f5_39
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step42 (hred : RedpartSound theRedpart) :
    SucceedsIn q5_8 p5_8l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s5_step41 hred
  intro L2_1
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s5_step34 hred L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s5_step43 (hred : RedpartSound theRedpart) :
    SucceedsIn p5_0 p5_0 := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact s5_step42 hred
    intro L1_1
    refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s5_step28 hred L1_1
  intro L0_1
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s5_step7 hred L0_1

end FourColor

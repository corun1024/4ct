import FourColor.Present10Hub2
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 10 presentation

A chunk of the case analysis of `present10.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step11 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q10_1) :
    SucceedsIn p10_0 p10_7r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step12 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q10_1) :
    SucceedsIn p10_0 p10_4r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step11 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step13 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q10_1) :
    SucceedsIn p10_0 p10_1r := by
  refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step12 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step29 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23)
    (L2_2 : Successful q10_24) :
    SucceedsIn q10_19 p10_26r := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step41 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23)
    (L3_1 : Successful q10_36) :
    SucceedsIn q10_24 p10_38r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_40

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step51 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_48 p10_48l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_50

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step52 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_36 p10_47r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s10_step51 hred L1_1 L1_2 L2_1
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_49

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step54 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_46 p10_46l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_53

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step55 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_36 p10_43r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s10_step54 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step52 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step57 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_43 p10_43l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_56

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step59 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_42 p10_42l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_58

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step60 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_24 p10_35r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s10_step59 hred L1_1 L1_2 L2_1
    intro _
    refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
    · exact s10_step57 hred L1_1 L1_2 L2_1
    intro _
    exact s10_step55 hred L1_1 L1_2 L2_1
  intro L3_1
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step41 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step62 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_35 p10_35l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_61

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step70 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_33 p10_33l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_69

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step72 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_24 p10_31r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_71
  intro _
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact s10_step70 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact h10_68 hred _
  intro _
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact s10_step62 hred L1_1 L1_2 L2_1
  intro _
  exact s10_step60 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step95 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L2_1 : Successful q10_23) :
    SucceedsIn q10_19 p10_23r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact h10_94 hred _
    intro _
    exact s10_step72 hred L1_1 L1_2 L2_1
  intro L2_2
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step29 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step129 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_126r := by
  refine succeed_by_split .fan2 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_128

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step130 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_122r := by
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step129 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step131 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_118r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step130 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step132 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_114r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step131 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step133 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_110r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 9 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step132 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step134 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_107r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step133 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step135 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101)
    (L3_2 : Successful q10_103) :
    SucceedsIn q10_23 p10_104r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step134 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step143 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101) :
    SucceedsIn q10_103 p10_140r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 4 <|
     Hubcap.two 3 6 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_142

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step145 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101) :
    SucceedsIn q10_103 p10_136r := by
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 0 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_144
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step143 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step147 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L3_1 : Successful q10_101) :
    SucceedsIn q10_103 p10_103l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 3 8 8 <|
       Hubcap.two 6 9 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_146
  intro _
  exact s10_step145 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step167 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149)
    (L4_2 : Successful q10_157) :
    SucceedsIn q10_164 p10_164l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_166

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149)
    (L4_2 : Successful q10_157) :
    SucceedsIn q10_101 p10_163r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step167 hred L1_1 L1_2 L4_1 L4_2
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_165

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step169 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149)
    (L4_2 : Successful q10_157) :
    SucceedsIn q10_101 p10_159r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step168 hred L1_1 L1_2 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step179 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_176 p10_176l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_178

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step180 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_157 p10_175r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step179 hred L1_1 L1_2 L4_1
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step182 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_174 p10_174l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step183 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_157 p10_171r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact s10_step182 hred L1_1 L1_2 L4_1
  intro _
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step180 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step185 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_157 p10_157l := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 1 8 8 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 7 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_184
  intro _
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step183 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step186 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_101 p10_155r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact s10_step185 hred L1_1 L1_2 L4_1
  intro L4_2
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step169 hred L1_1 L1_2 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step188 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_101 p10_154r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 9 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_187
  intro _
  exact s10_step186 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step190 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_101 p10_152r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 9 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_189
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step188 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step192 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_151 p10_151l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_191

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step194 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16)
    (L4_1 : Successful q10_149) :
    SucceedsIn q10_101 p10_149r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 6 9 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_193
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s10_step192 hred L1_1 L1_2 L4_1
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step190 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step206 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_203 p10_203l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_205

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step207 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_149 p10_202r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s10_step206 hred L1_1 L1_2
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_204

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step209 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_149 p10_201r := by
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_208
  intro _
  exact s10_step207 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step211 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_200 p10_200l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_210

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step213 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_198 p10_198l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_212

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step214 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_149 p10_197r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step213 hred L1_1 L1_2
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s10_step211 hred L1_1 L1_2
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step209 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step216 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_197 p10_197l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_215

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step218 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_196 p10_196l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_217

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step220 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_195 p10_195l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_219

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step221 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_101 p10_148r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s10_step220 hred L1_1 L1_2
    intro _
    refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
    · exact s10_step218 hred L1_1 L1_2
    intro _
    refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
    · exact s10_step216 hred L1_1 L1_2
    intro _
    exact s10_step214 hred L1_1 L1_2
  intro L4_1
  exact s10_step194 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step223 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_101 p10_101l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 9 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_222
  intro _
  exact s10_step221 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step224 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_100r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s10_step223 hred L1_1 L1_2
  intro L3_1
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact s10_step147 hred L1_1 L1_2 L3_1
  intro L3_2
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step135 hred L1_1 L1_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step226 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_99r := by
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 3 6 9 <|
       Hubcap.two 8 9 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_225
  intro _
  exact s10_step224 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step228 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_98r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 8 3 <|
       Hubcap.one 9 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_227
  intro _
  exact s10_step226 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step230 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_97r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_229
  intro _
  exact s10_step228 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step232 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_96r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 6 9 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_231
  intro _
  exact s10_step230 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step234 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_23 p10_23l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 9 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_233
  intro _
  exact s10_step232 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step235 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_1 p10_18r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
    · exact s10_step234 hred L1_1 L1_2
    intro L2_1
    exact s10_step95 hred L1_1 L1_2 L2_1
  intro L1_3
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_similarity 8 false L1_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step243 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_18 p10_240r := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_242

end FourColor

import FourColor.Present9Hub6
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step11 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q9_1) :
    SucceedsIn p9_0 p9_8r := by
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step12 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q9_1) :
    SucceedsIn p9_0 p9_5r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step11 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step13 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q9_1) :
    SucceedsIn p9_0 p9_2r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step12 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step23 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18)
    (L1_4 : Successful q9_20) :
    SucceedsIn q9_1 p9_20r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step52 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_48r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_51
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_50

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step54 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_45r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_53
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step52 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step56 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_43r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_55
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step54 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step58 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_41r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_57
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step56 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step60 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_39r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 5 8 5 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_59
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step58 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step62 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_38r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 4 6 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_61
  intro _
  exact s9_step60 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step64 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_37r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_63
  intro _
  exact s9_step62 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step66 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_35r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_65
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step64 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step68 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_33r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_67
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step66 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step70 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_32r := by
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
      rfl (by decide +kernel) (by decide +kernel) f9_69
  intro _
  exact s9_step68 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step72 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_31r := by
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
      rfl (by decide +kernel) (by decide +kernel) f9_71
  intro _
  exact s9_step70 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step75 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_29r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_74
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_73
  intro _
  exact s9_step72 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step78 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_27r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_77
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_76
  intro _
  exact s9_step75 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step80 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_26r := by
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
      rfl (by decide +kernel) (by decide +kernel) f9_79
  intro _
  exact s9_step78 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step82 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_25r := by
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
      rfl (by decide +kernel) (by decide +kernel) f9_81
  intro _
  exact s9_step80 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step84 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L1_3 : Successful q9_18) :
    SucceedsIn q9_20 p9_24r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_83
  intro _
  exact s9_step82 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step108 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_104r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 1 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_107
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_106

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step111 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_102r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_110
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 7 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_109
  intro _
  exact s9_step108 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step113 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_101r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_112
  intro _
  exact s9_step111 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step115 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_99r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_114
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step113 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step117 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_98r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_116
  intro _
  exact s9_step115 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step119 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_97r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_118
  intro _
  exact s9_step117 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step122 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_95r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_121
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_120
  intro _
  exact s9_step119 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step124 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_94r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_123
  intro _
  exact s9_step122 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step126 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_93r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_125
  intro _
  exact s9_step124 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step128 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_92r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_127
  intro _
  exact s9_step126 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step131 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_90r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_130
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_129
  intro _
  exact s9_step128 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step134 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_88r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_133
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_132
  intro _
  exact s9_step131 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step136 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L2_1 : Successful q9_86) :
    SucceedsIn q9_18 p9_87r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_135
  intro _
  exact s9_step134 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step166 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_162r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_165
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_164

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_161r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_167
  intro _
  exact s9_step166 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step170 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_160r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_169
  intro _
  exact s9_step168 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step172 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_158r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_171
  intro _
  exact s9_step170 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step186 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_155r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_185
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact h9_184 hred _
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact h9_178 hred _
  intro _
  exact s9_step172 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step189 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_153r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_188
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_187
  intro _
  exact s9_step186 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step191 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_152r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_190
  intro _
  exact s9_step189 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step193 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_151r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_192
  intro _
  exact s9_step191 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step196 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_149r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 3 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_195
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.two 0 1 6 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 6 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_194
  intro _
  exact s9_step193 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step217 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_213r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_216
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_215

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step219 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_212r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_218
  intro _
  exact s9_step217 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step221 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_210r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_220
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step219 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step223 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_208r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 4 7 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_222
  intro _
  exact s9_step221 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step226 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_206r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 7 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_225
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 8 7 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_224
  intro _
  exact s9_step223 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step229 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_204r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 2 6 7 <|
       Hubcap.two 3 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_228
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_227
  intro _
  exact s9_step226 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step232 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_202r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_231
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 5 <|
       Hubcap.two 0 8 5 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_230
  intro _
  exact s9_step229 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step235 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_200r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_234
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_233
  intro _
  exact s9_step232 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step237 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_199r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_236
  intro _
  exact s9_step235 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step239 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_198r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_238
  intro _
  exact s9_step237 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step242 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_149 p9_149l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_241
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_240
  intro _
  exact s9_step239 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step250 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_148 p9_246r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_249
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_248

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step252 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_148 p9_245r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_251
  intro _
  exact s9_step250 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step254 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_148 p9_244r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_253
  intro _
  exact s9_step252 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step256 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_148 p9_243r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_255
  intro _
  exact s9_step254 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step266 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_147 p9_262r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_265
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_264

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step268 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_147 p9_260r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 2 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_267
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step266 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step270 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_147 p9_259r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_269
  intro _
  exact s9_step268 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step272 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_147 p9_258r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 4 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_271
  intro _
  exact s9_step270 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step274 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_147 p9_257r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 4 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_273
  intro _
  exact s9_step272 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step275 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_146r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step274 hred L1_1 L1_2 L3_1
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step256 hred L1_1 L1_2 L3_1
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact s9_step242 hred L1_1 L1_2 L3_1
  intro _
  exact s9_step196 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step277 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16)
    (L3_1 : Successful q9_144) :
    SucceedsIn q9_86 p9_144r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_276
  intro _
  exact s9_step275 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step288 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_284r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_287
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_286

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step290 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_283r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_289
  intro _
  exact s9_step288 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step292 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_281r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_291
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step290 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step294 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_280r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_293
  intro _
  exact s9_step292 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step296 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_279r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_295
  intro _
  exact s9_step294 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step298 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_278r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_297
  intro _
  exact s9_step296 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step300 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_144 p9_144l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_299
  intro _
  exact s9_step298 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step302 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_142r := by
  refine succeed_by_split .spoke 7 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 0 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_301
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step300 hred L1_1 L1_2
  intro L3_1
  exact s9_step277 hred L1_1 L1_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step304 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_141r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_303
  intro _
  exact s9_step302 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step306 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_140r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_305
  intro _
  exact s9_step304 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step308 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_139r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_307
  intro _
  exact s9_step306 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step310 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_138r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_309
  intro _
  exact s9_step308 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step312 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_86 p9_137r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 4 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_311
  intro _
  exact s9_step310 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step313 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_18 p9_18l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_2
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step312 hred L1_1 L1_2
  intro L2_1
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step136 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L1_2 : Successful q9_16) :
    SucceedsIn q9_1 p9_17r := by
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact s9_step313 hred L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step84 hred L1_1 L1_2 L1_3
  intro L1_4
  exact s9_step23 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L2_1 : Successful q9_318) :
    SucceedsIn q9_16 p9_325r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_328
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.two 2 3 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 4 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_327

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step332 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L2_1 : Successful q9_318) :
    SucceedsIn q9_16 p9_323r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_331
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_330
  intro _
  exact s9_step329 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step335 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L2_1 : Successful q9_318) :
    SucceedsIn q9_16 p9_321r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_334
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_333
  intro _
  exact s9_step332 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step338 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L2_1 : Successful q9_318) :
    SucceedsIn q9_16 p9_319r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_337
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_336
  intro _
  exact s9_step335 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step354 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_346) :
    SucceedsIn q9_318 p9_350r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_353
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_352

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step356 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_346) :
    SucceedsIn q9_318 p9_349r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 2 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_355
  intro _
  exact s9_step354 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step358 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_346) :
    SucceedsIn q9_318 p9_348r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_357
  intro _
  exact s9_step356 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step360 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L3_1 : Successful q9_346) :
    SucceedsIn q9_318 p9_347r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_359
  intro _
  exact s9_step358 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step381 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365)
    (L4_2 : Successful q9_371) :
    SucceedsIn q9_346 p9_377r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_380
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_379

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step383 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365)
    (L4_2 : Successful q9_371) :
    SucceedsIn q9_346 p9_376r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_382
  intro _
  exact s9_step381 hred L1_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step385 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365)
    (L4_2 : Successful q9_371) :
    SucceedsIn q9_346 p9_374r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_384
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step383 hred L1_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step387 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365)
    (L4_2 : Successful q9_371) :
    SucceedsIn q9_346 p9_373r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 5 6 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_386
  intro _
  exact s9_step385 hred L1_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step389 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365)
    (L4_2 : Successful q9_371) :
    SucceedsIn q9_346 p9_372r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 5 7 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_388
  intro _
  exact s9_step387 hred L1_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step393 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_371 p9_371l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_392
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_391

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step398 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_370 p9_394r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_397
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_396

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step399 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_346 p9_369r := by
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step398 hred L1_1 L4_1
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step393 hred L1_1 L4_1
  intro L4_2
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step389 hred L1_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step401 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_346 p9_367r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.two 5 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_400
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step399 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step409 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_367 p9_405r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_408
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_407

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step411 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_367 p9_404r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_410
  intro _
  exact s9_step409 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step413 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_367 p9_403r := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_412
  intro _
  exact s9_step411 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step415 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_367 p9_402r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_414
  intro _
  exact s9_step413 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step431 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_427r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 7 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_430
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_429

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step433 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_426r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 7 8 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_432
  intro _
  exact s9_step431 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step435 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_424r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_434
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step433 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step437 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_423r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_436
  intro _
  exact s9_step435 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step439 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_421r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_438
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step437 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step441 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_419r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 7 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_440
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step439 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step443 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_418r := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_442
  intro _
  exact s9_step441 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step445 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_417r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_444
  intro _
  exact s9_step443 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step447 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_366 p9_416r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_446
  intro _
  exact s9_step445 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step448 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14)
    (L4_1 : Successful q9_365) :
    SucceedsIn q9_346 p9_365r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step447 hred L1_1 L4_1
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step415 hred L1_1 L4_1
  intro _
  exact s9_step401 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step462 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_458r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_461
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_460

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step464 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_456r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_463
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step462 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step466 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_454r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.two 3 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_465
  intro _
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step464 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step468 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_452r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_467
  intro _
  refine succeed_by_split .fan2 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step466 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step471 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_450r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 4 <|
       Hubcap.two 1 5 6 <|
       Hubcap.two 3 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_470
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.two 2 4 8 <|
       Hubcap.two 5 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_469
  intro _
  exact s9_step468 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step474 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_365 p9_365l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.two 2 4 8 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_473
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 4 8 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_472
  intro _
  exact s9_step471 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step481 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_364 p9_477r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_480
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_479

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_364 p9_476r := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_482
  intro _
  exact s9_step481 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step485 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_364 p9_475r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_484
  intro _
  exact s9_step483 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step487 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_364 p9_364l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_486
  intro _
  exact s9_step485 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step492 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_363 p9_488r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_491
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_490

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step494 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_363 p9_363l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_493
  intro _
  exact s9_step492 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step512 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_508r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_511
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_510

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step514 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_506r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_513
  intro _
  refine succeed_by_split .fan2 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step512 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step516 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_504r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_515
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step514 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step518 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_503r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 2 <|
       Hubcap.two 1 2 8 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_517
  intro _
  exact s9_step516 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step520 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_502r := by
  refine succeed_by_split .spoke 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 2 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_519
  intro _
  exact s9_step518 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step522 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_501r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_521
  intro _
  exact s9_step520 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step533 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_529r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_532
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_531

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step535 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_527r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_534
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step533 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step537 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_526r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_536
  intro _
  exact s9_step535 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step539 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_525r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_538
  intro _
  exact s9_step537 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step541 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_523r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 1 8 5 <|
       Hubcap.two 2 5 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_540
  intro _
  exact s9_step539 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step543 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_499 p9_499l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_542
  intro _
  exact s9_step541 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step545 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_497r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.two 1 8 6 <|
       Hubcap.two 2 4 8 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_544
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s9_step543 hred L1_1
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step522 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step548 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_495r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_547
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 4 8 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_546
  intro _
  exact s9_step545 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step550 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_362 p9_362l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_549
  intro _
  exact s9_step548 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step551 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_346 p9_361r := by
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact s9_step550 hred L1_1
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s9_step494 hred L1_1
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact s9_step487 hred L1_1
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s9_step474 hred L1_1
  intro L4_1
  exact s9_step448 hred L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step553 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_346 p9_346l := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 5 8 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_552
  intro _
  exact s9_step551 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step555 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_318 p9_344r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 7 0 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 2 5 8 <|
       Hubcap.two 3 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_554
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact s9_step553 hred L1_1
  intro L3_1
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step360 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step585 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_581r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_584
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_583

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step587 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_580r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_586
  intro _
  exact s9_step585 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step592 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_578 p9_588r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_591
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_590

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step594 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_578 p9_578l := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_593
  intro _
  exact s9_step592 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step595 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_576r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s9_step594 hred L1_1
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step587 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step597 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_574r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_596
  intro _
  exact s9_step595 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step599 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_573r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_598
  intro _
  exact s9_step597 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step608 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_572 p9_604r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.two 1 8 6 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_607
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_606

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step610 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_572 p9_602r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_609
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step608 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step612 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_572 p9_601r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_611
  intro _
  exact s9_step610 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step614 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_572 p9_572l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 3 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_613
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step612 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step616 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_570r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_615
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact s9_step614 hred L1_1
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step599 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step618 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_568r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_617
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step616 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step620 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_566r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 5 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_619
  intro _
  exact s9_step618 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step623 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_564r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_622
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_621
  intro _
  exact s9_step620 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step626 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_343 p9_562r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_625
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_624
  intro _
  exact s9_step623 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step641 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q9_14) :
    SucceedsIn q9_561 p9_637r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_640
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_639

end FourColor

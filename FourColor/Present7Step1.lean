import FourColor.Present7Hub1
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step23 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8)
    (L0_3 : Successful q7_15) :
    SucceedsIn p7_0 p7_19r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step24 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8)
    (L0_3 : Successful q7_15) :
    SucceedsIn p7_0 p7_16r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step23 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step31 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8) :
    SucceedsIn q7_15 p7_27r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_30
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step33 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8) :
    SucceedsIn q7_15 p7_25r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 1 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_32
  intro _
  exact s7_step31 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step34 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8) :
    SucceedsIn p7_0 p7_13r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step33 hred L0_1 L0_2
  intro L0_3
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step24 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step35 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L0_2 : Successful q7_8) :
    SucceedsIn p7_0 p7_10r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step34 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step59 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41)
    (L1_5 : Successful q7_48) :
    SucceedsIn q7_8 p7_55r := by
  refine succeed_by_split .fan1 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_58
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_57

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step62 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41)
    (L1_5 : Successful q7_48) :
    SucceedsIn q7_8 p7_53r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_61
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 2 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_60
  intro _
  exact s7_step59 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step65 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41)
    (L1_5 : Successful q7_48) :
    SucceedsIn q7_8 p7_51r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_64
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_63
  intro _
  exact s7_step62 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step68 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41)
    (L1_5 : Successful q7_48) :
    SucceedsIn q7_8 p7_49r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_67
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_66
  intro _
  exact s7_step65 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step72 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41) :
    SucceedsIn q7_48 p7_48l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_71
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 6 1 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_70

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step74 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41) :
    SucceedsIn q7_8 p7_46r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 6 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_73
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s7_step72 hred L0_1 L1_1 L1_2 L1_3 L1_4
  intro L1_5
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step68 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step77 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41) :
    SucceedsIn q7_8 p7_44r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 6 2 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_76
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_75
  intro _
  exact s7_step74 hred L0_1 L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step80 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39)
    (L1_4 : Successful q7_41) :
    SucceedsIn q7_8 p7_42r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_79
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_78
  intro _
  exact s7_step77 hred L0_1 L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step98 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_94r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_97
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_96

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step99 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_90r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step98 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step106 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_88 p7_102r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_105
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_104

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step109 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_88 p7_100r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_108
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_107
  intro _
  exact s7_step106 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step111 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_87r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.two 1 4 3 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 5 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_110
    intro _
    exact s7_step109 hred L0_1 L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step99 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step114 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_85r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_113
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_112
  intro _
  exact s7_step111 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step117 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_83r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_116
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_115
  intro _
  exact s7_step114 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step119 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_41 p7_81r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_118
  intro _
  exact s7_step117 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step120 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38)
    (L1_3 : Successful q7_39) :
    SucceedsIn q7_8 p7_39r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L1_2
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step119 hred L0_1 L1_1 L1_2 L1_3
  intro L1_4
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step80 hred L0_1 L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step140 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_136r := by
  refine succeed_by_split .fan1 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_139
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_138

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step143 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_134r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_142
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_141
  intro _
  exact s7_step140 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step146 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_132r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_145
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_144
  intro _
  exact s7_step143 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step149 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_130r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_148
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_147
  intro _
  exact s7_step146 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step152 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_128r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_151
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_150
  intro _
  exact s7_step149 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step155 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_126r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_154
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_153
  intro _
  exact s7_step152 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step158 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_124r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_157
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_156
  intro _
  exact s7_step155 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step160 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L1_2 : Successful q7_38) :
    SucceedsIn q7_39 p7_122r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_159
  intro _
  exact s7_step158 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step188 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168)
    (L2_4 : Successful q7_181) :
    SucceedsIn q7_38 p7_184r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_187

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step194 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_181 p7_190r := by
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_193
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_192

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step196 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_181 p7_181l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_195
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step194 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step197 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_38 p7_180r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step196 hred L0_1 L1_1 L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step188 hred L0_1 L1_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step200 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_38 p7_178r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_199
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_198
  intro _
  exact s7_step197 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step203 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_38 p7_176r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_202
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_201
  intro _
  exact s7_step200 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step205 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_38 p7_174r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_204
  intro _
  exact s7_step203 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step206 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166)
    (L2_3 : Successful q7_168) :
    SucceedsIn q7_38 p7_170r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step205 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step219 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_168 p7_215r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_218
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_217

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step221 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_168 p7_213r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_220
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step219 hred L0_1 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step224 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_168 p7_211r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_223
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_222
  intro _
  exact s7_step221 hred L0_1 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step227 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_168 p7_209r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 6 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_226
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_225
  intro _
  exact s7_step224 hred L0_1 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step229 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_168 p7_207r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_228
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step227 hred L0_1 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step231 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164)
    (L2_2 : Successful q7_166) :
    SucceedsIn q7_38 p7_167r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 3 <|
         Hubcap.two 3 6 3 <|
         Hubcap.two 4 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_230
    intro _
    exact s7_step229 hred L0_1 L1_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step206 hred L0_1 L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step239 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164) :
    SucceedsIn q7_166 p7_235r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_238
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_237

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step242 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164) :
    SucceedsIn q7_166 p7_233r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_241
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_240
  intro _
  exact s7_step239 hred L0_1 L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step244 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36)
    (L2_1 : Successful q7_164) :
    SucceedsIn q7_166 p7_166l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_243
  intro _
  exact s7_step242 hred L0_1 L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step259 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_255r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_258
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_257

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step262 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_253r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_261
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_260
  intro _
  exact s7_step259 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step265 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_251r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 3 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_264
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_263
  intro _
  exact s7_step262 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step268 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_249r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_267
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_266
  intro _
  exact s7_step265 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step270 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_247r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_269
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step268 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step273 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_164 p7_245r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_272
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_271
  intro _
  exact s7_step270 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step274 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_38 p7_163r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step273 hred L0_1 L1_1
  intro L2_1
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step244 hred L0_1 L1_1 L2_1
  intro L2_2
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step231 hred L0_1 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step294 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_290r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_293
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_292

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step296 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_288r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_295
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step294 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step298 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_286r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_297
  intro _
  exact s7_step296 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step300 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_284r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_299
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step298 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step302 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_282r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_301
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step300 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step305 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_280r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 5 4 <|
       Hubcap.two 2 6 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_304
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_303
  intro _
  exact s7_step302 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step307 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_278r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_306
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step305 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step310 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_163 p7_276r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_309
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_308
  intro _
  exact s7_step307 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step312 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_38 p7_161r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_311
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step310 hred L0_1 L1_1
  intro _
  exact s7_step274 hred L0_1 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step314 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L1_1 : Successful q7_36) :
    SucceedsIn q7_8 p7_37r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 4 <|
         Hubcap.two 0 5 6 <|
         Hubcap.two 0 6 4 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_313
    intro _
    exact s7_step312 hred L0_1 L1_1
  intro L1_2
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 2 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step160 hred L0_1 L1_1 L1_2
  intro L1_3
  exact s7_step120 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step334 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L2_6 : Successful q7_326) :
    SucceedsIn q7_36 p7_330r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_333
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_332

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step335 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L2_6 : Successful q7_326) :
    SucceedsIn q7_36 p7_326r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step334 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step354 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338)
    (L3_2 : Successful q7_346) :
    SucceedsIn q7_326 p7_350r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_353
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_352

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step356 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338)
    (L3_2 : Successful q7_346) :
    SucceedsIn q7_326 p7_348r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_355
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step354 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step358 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338)
    (L3_2 : Successful q7_346) :
    SucceedsIn q7_326 p7_346r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_357
  intro _
  exact s7_step356 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step366 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_346 p7_362r := by
  refine succeed_by_split .fan1 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_365
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_364

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step369 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_346 p7_360r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_368
  intro _
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_367
  intro _
  exact s7_step366 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step372 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_346 p7_346l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_371
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_370
  intro _
  exact s7_step369 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step374 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_326 p7_344r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_373
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s7_step372 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1
  intro L3_2
  exact s7_step358 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step376 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_326 p7_341r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.two 0 6 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_375
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step374 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step385 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_341 p7_381r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_384
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_383

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step388 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_341 p7_379r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 3 7 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_387
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 1 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_386
  intro _
  exact s7_step385 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step391 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_341 p7_377r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_390
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.two 0 4 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_389
  intro _
  exact s7_step388 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step397 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_340 p7_393r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_396
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_395

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step399 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_340 p7_340l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_398
  intro _
  exact s7_step397 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step401 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_338) :
    SucceedsIn q7_326 p7_338r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_400
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step399 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step391 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1
  intro _
  exact s7_step376 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step406 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_338 p7_402r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_405

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step408 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_326 p7_336r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_407
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step406 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro L3_1
  exact s7_step401 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step421 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_336 p7_417r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_420
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_419

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step423 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_336 p7_415r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_422
  intro _
  exact s7_step421 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step426 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_336 p7_413r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_425
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_424
  intro _
  exact s7_step423 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step428 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_336 p7_412r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_427
  intro _
  exact s7_step426 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step434 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_411 p7_430r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_433
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_432

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step436 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_411 p7_411l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_435
  intro _
  exact s7_step434 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step438 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_336 p7_409r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.two 0 6 3 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_437
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step436 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step428 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step440 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_326 p7_326l := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 1 3 4 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_439
    intro _
    exact s7_step438 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step408 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step460 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_456r := by
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_459

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step462 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_455r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_461
  intro _
  exact s7_step460 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step465 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_453r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_464
  intro _
  refine succeed_by_split .fan1 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_463
  intro _
  exact s7_step462 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step468 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_451r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_467
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_466
  intro _
  exact s7_step465 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step470 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_449r := by
  refine succeed_by_split .fan2 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_469
  intro _
  exact s7_step468 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step481 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_449 p7_477r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_480
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_479

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step484 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_449 p7_475r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_483
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_482
  intro _
  exact s7_step481 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step487 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_449 p7_473r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_486
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_485
  intro _
  exact s7_step484 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step490 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_449 p7_471r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_489
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_488
  intro _
  exact s7_step487 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step492 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323)
    (L3_1 : Successful q7_447) :
    SucceedsIn q7_325 p7_448r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 0 <|
         Hubcap.two 3 5 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_491
    intro _
    exact s7_step490 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1
  intro _
  exact s7_step470 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step501 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_447 p7_497r := by
  refine succeed_by_split .fan1 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_500
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_499

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step504 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_447 p7_495r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_503
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_502
  intro _
  exact s7_step501 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step507 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_447 p7_493r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_506
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_505
  intro _
  exact s7_step504 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step509 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_325 p7_446r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 4 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 0 <|
         Hubcap.two 0 5 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_508
    intro _
    exact s7_step507 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro L3_1
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step492 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step515 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_446 p7_511r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_514
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_513

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step517 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_446 p7_510r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_516
  intro _
  exact s7_step515 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step519 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_325 p7_445r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 1 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 3 <|
         Hubcap.one 6 0 <|
         Hubcap.two 1 3 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_518
    intro _
    exact s7_step517 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step509 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step523 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_445 p7_445l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_522
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_521

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step525 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_325 p7_443r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_524
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact s7_step523 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s7_step519 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step527 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_325 p7_441r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_526
  intro _
  exact s7_step525 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step528 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321)
    (L2_5 : Successful q7_323) :
    SucceedsIn q7_36 p7_323r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step527 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s7_step440 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro L2_6
  exact s7_step335 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step540 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321) :
    SucceedsIn q7_323 p7_536r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_539
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_538

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step543 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321) :
    SucceedsIn q7_323 p7_534r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_542
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 6 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_541
  intro _
  exact s7_step540 hred L0_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step546 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321) :
    SucceedsIn q7_323 p7_532r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_545
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_544
  intro _
  exact s7_step543 hred L0_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step549 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321) :
    SucceedsIn q7_323 p7_530r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_548
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_547
  intro _
  exact s7_step546 hred L0_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step551 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319)
    (L2_4 : Successful q7_321) :
    SucceedsIn q7_323 p7_323l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_550
  intro _
  exact s7_step549 hred L0_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step560 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319) :
    SucceedsIn q7_321 p7_556r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_559
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_558

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step563 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319) :
    SucceedsIn q7_321 p7_554r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_562
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_561
  intro _
  exact s7_step560 hred L0_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step566 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319) :
    SucceedsIn q7_321 p7_552r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_565
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_564
  intro _
  exact s7_step563 hred L0_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step568 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318)
    (L2_3 : Successful q7_319) :
    SucceedsIn q7_36 p7_320r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 3 4 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 2 <|
         Hubcap.one 6 2 <|
         Hubcap.two 1 2 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_567
    intro _
    exact s7_step566 hred L0_1 L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s7_step551 hred L0_1 L2_1 L2_2 L2_3 L2_4
  intro L2_5
  exact s7_step528 hred L0_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step573 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316)
    (L2_2 : Successful q7_318) :
    SucceedsIn q7_319 p7_569r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_572

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step598 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_594r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_597
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_596

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step600 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_592r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_599
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step598 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step602 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_589r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_601
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step600 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step605 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_587r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_604
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_603
  intro _
  exact s7_step602 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step608 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_318 p7_585r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_607
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_606
  intro _
  exact s7_step605 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step623 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_619r := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.two 3 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_622
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_621

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step626 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_617r := by
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
      rfl (by decide +kernel) (by decide +kernel) f7_625
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.two 3 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_624
  intro _
  exact s7_step623 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step628 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_615r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_627
  intro _
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step626 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step631 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_613r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.two 3 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_630
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_629
  intro _
  exact s7_step628 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step634 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_611r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 3 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_633
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_632
  intro _
  exact s7_step631 hred L0_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step636 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q7_1)
    (L2_1 : Successful q7_316) :
    SucceedsIn q7_584 p7_609r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.two 3 6 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_635
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step634 hred L0_1 L2_1

end FourColor

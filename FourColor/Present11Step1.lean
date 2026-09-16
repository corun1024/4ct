import FourColor.Present11Hub1
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 11 presentation

A chunk of the case analysis of `present11.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step34 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L0_3 : Successful q11_23) :
    SucceedsIn p11_0 p11_30r := by
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 10 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 10 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step35 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L0_3 : Successful q11_23) :
    SucceedsIn p11_0 p11_27r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step34 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step36 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L0_3 : Successful q11_23) :
    SucceedsIn p11_0 p11_24r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step35 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step62 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_58r := by
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step63 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_55r := by
  refine succeed_by_split .hat 10 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step62 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step64 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_52r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 9 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step63 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step65 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_49r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step64 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step66 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_46r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step65 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step67 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_43r := by
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step66 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step68 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L1_2 : Successful q11_39) :
    SucceedsIn q11_23 p11_40r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step67 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step77 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L2_1 : Successful q11_69)
    (L2_2 : Successful q11_71) :
    SucceedsIn q11_39 p11_74r := by
  refine succeed_by_split .spoke 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_76

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step78 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L2_1 : Successful q11_69)
    (L2_2 : Successful q11_71) :
    SucceedsIn q11_39 p11_71r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step77 hred L0_1 L0_2 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step82 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L2_1 : Successful q11_69) :
    SucceedsIn q11_71 p11_79r := by
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step90 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L3_1 : Successful q11_83)
    (L3_2 : Successful q11_85) :
    SucceedsIn q11_69 p11_87r := by
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_89

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step95 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L3_1 : Successful q11_83)
    (L4_1 : Successful q11_91) :
    SucceedsIn q11_85 p11_92r := by
  refine succeed_by_split .spoke 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_94

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step99 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L3_1 : Successful q11_83) :
    SucceedsIn q11_91 p11_96r := by
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_98

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step100 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L3_1 : Successful q11_83) :
    SucceedsIn q11_69 p11_84r := by
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 8 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 4 false L3_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s11_step99 hred L0_1 L0_2 L1_1 L3_1
    intro L4_1
    refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step95 hred L0_1 L0_2 L1_1 L3_1 L4_1
  intro L3_2
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step90 hred L0_1 L0_2 L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step107 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L4_1 : Successful q11_101) :
    SucceedsIn q11_83 p11_104r := by
  refine succeed_by_split .spoke 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_106

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step109 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L4_1 : Successful q11_101) :
    SucceedsIn q11_104 p11_104l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_108

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step111 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L4_1 : Successful q11_101) :
    SucceedsIn q11_103 p11_103l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 8 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_110

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step129 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L5_1 : Successful q11_124) :
    SucceedsIn q11_101 p11_126r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 2 4 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_128

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step136 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_133 p11_133l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_135

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step137 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_124 p11_132r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s11_step136 hred L0_1 L0_2 L1_1
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_134

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step139 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_130 p11_130l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_138

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step140 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_101 p11_123r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
    · exact s11_step139 hred L0_1 L0_2 L1_1
    intro _
    refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 10 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s11_step137 hred L0_1 L0_2 L1_1
  intro L5_1
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step129 hred L0_1 L0_2 L1_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step142 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_122 p11_122l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_141

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step144 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_120 p11_120l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_143

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step145 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_101 p11_119r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact s11_step144 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s11_step142 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step140 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step147 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_118 p11_118l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_146

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step149 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_116 p11_116l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_148

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step150 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_101 p11_115r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s11_step149 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact s11_step147 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step145 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step152 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_115 p11_115l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_151

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step154 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_114 p11_114l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step171 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L6_1 : Successful q11_166) :
    SucceedsIn q11_112 p11_168r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 7 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_170

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step178 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_175 p11_175l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step179 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_166 p11_174r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s11_step178 hred L0_1 L0_2 L1_1
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step181 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_172 p11_172l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_180

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step182 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_112 p11_165r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
    · exact s11_step181 hred L0_1 L0_2 L1_1
    intro _
    refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 10 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s11_step179 hred L0_1 L0_2 L1_1
  intro L6_1
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step171 hred L0_1 L0_2 L1_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step184 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_164 p11_164l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_183

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step186 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_162 p11_162l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_185

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step187 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_112 p11_161r := by
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact s11_step186 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s11_step184 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step182 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step189 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_160 p11_160l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_188

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step191 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_158 p11_158l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_190

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step192 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_112 p11_157r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s11_step191 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact s11_step189 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step187 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step194 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_157 p11_157l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 9 5 <|
     Hubcap.two 8 10 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step212 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L7_1 : Successful q11_205) :
    SucceedsIn q11_209 p11_209l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_211

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step213 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37)
    (L7_1 : Successful q11_205) :
    SucceedsIn q11_155 p11_208r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s11_step212 hred L0_1 L0_2 L1_1 L7_1
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_210

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step220 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_217 p11_217l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_219

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step221 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_205 p11_216r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s11_step220 hred L0_1 L0_2 L1_1
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 8 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_218

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step223 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_214 p11_214l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_222

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step224 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_155 p11_204r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
    · exact s11_step223 hred L0_1 L0_2 L1_1
    intro _
    refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 10 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s11_step221 hred L0_1 L0_2 L1_1
  intro L7_1
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L7_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step213 hred L0_1 L0_2 L1_1 L7_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step226 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_203 p11_203l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_225

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step228 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_201 p11_201l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_227

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step229 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_155 p11_200r := by
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact s11_step228 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s11_step226 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step224 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step231 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_199 p11_199l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_230

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step233 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_197 p11_197l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_232

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step234 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_155 p11_196r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s11_step233 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact s11_step231 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s11_step229 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step235 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_112 p11_112l := by
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 8 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 8 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step234 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · exact s11_step194 hred L0_1 L0_2 L1_1
  intro _
  exact s11_step192 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step236 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_101 p11_101l := by
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact s11_step235 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact s11_step154 hred L0_1 L0_2 L1_1
  intro _
  refine succeed_by_split .spoke 9 5 false (by decide +kernel) ?_ ?_
  · exact s11_step152 hred L0_1 L0_2 L1_1
  intro _
  exact s11_step150 hred L0_1 L0_2 L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step237 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_83 p11_83l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact s11_step236 hred L0_1 L0_2 L1_1
  intro L4_1
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact s11_step111 hred L0_1 L0_2 L1_1 L4_1
  intro _
  refine succeed_by_split .spoke 8 5 false (by decide +kernel) ?_ ?_
  · exact s11_step109 hred L0_1 L0_2 L1_1 L4_1
  intro _
  exact s11_step107 hred L0_1 L0_2 L1_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step238 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12)
    (L1_1 : Successful q11_37) :
    SucceedsIn q11_39 p11_39l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact s11_step237 hred L0_1 L0_2 L1_1
    intro L3_1
    refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step100 hred L0_1 L0_2 L1_1 L3_1
  intro L2_1
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step82 hred L0_1 L0_2 L1_1 L2_1
  intro L2_2
  exact s11_step78 hred L0_1 L0_2 L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step250 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn q11_242 p11_242l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_249

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step252 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn q11_241 p11_241l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_251

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step254 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn q11_37 p11_239r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap11 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 5 <|
       Hubcap.one 9 5 <|
       Hubcap.one 10 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 4 5 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f11_253
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact s11_step252 hred L0_1 L0_2
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s11_step250 hred L0_1 L0_2
  intro _
  exact h11_248 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step256 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn q11_239 p11_239l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_255

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step257 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn q11_23 p11_23l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact s11_step256 hred L0_1 L0_2
    intro _
    exact s11_step254 hred L0_1 L0_2
  intro L1_1
  refine succeed_by_split .spoke 10 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 10 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact s11_step238 hred L0_1 L0_2 L1_1
  intro L1_2
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step68 hred L0_1 L0_2 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step258 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn p11_0 p11_20r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 10 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 10 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 5 false (by decide +kernel) ?_ ?_
  · exact s11_step257 hred L0_1 L0_2
  intro L0_3
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step36 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step259 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn p11_0 p11_17r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step258 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step260 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L0_2 : Successful q11_12) :
    SucceedsIn p11_0 p11_14r := by
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
  exact s11_step259 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step278 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_275 p11_275l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 7 8 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_277

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step279 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_12 p11_274r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact s11_step278 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 7 9 <|
     Hubcap.two 8 9 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_276

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step281 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_274 p11_274l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 7 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_280

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step283 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_273 p11_273l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 5 6 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step285 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_272 p11_272l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 4 5 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_284

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step287 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_271 p11_271l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 3 4 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_286

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step288 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267)
    (L1_5 : Successful q11_269) :
    SucceedsIn q11_12 p11_270r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact s11_step287 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact s11_step285 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact s11_step283 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s11_step281 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  exact s11_step279 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step292 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267) :
    SucceedsIn q11_269 p11_289r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_291

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step293 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265)
    (L1_4 : Successful q11_267) :
    SucceedsIn q11_12 p11_267r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 true L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step292 hred L0_1 L1_1 L1_2 L1_3 L1_4
  intro L1_5
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step288 hred L0_1 L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step299 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265) :
    SucceedsIn q11_267 p11_296r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_298

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step300 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263)
    (L1_3 : Successful q11_265) :
    SucceedsIn q11_267 p11_267l := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step299 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step305 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263) :
    SucceedsIn q11_265 p11_302r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_304

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step306 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261)
    (L1_2 : Successful q11_263) :
    SucceedsIn q11_12 p11_264r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 true L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s11_step305 hred L0_1 L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s11_step300 hred L0_1 L1_1 L1_2 L1_3
  intro L1_4
  exact s11_step293 hred L0_1 L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step309 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1)
    (L1_1 : Successful q11_261) :
    SucceedsIn q11_263 p11_263l := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_308

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step311 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn q11_261 p11_261l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_310

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step312 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn q11_12 p11_12l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s11_step311 hred L0_1
  intro L1_1
  refine succeed_by_split .spoke 10 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 10 true L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s11_step309 hred L0_1 L1_1
  intro L1_2
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step306 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step313 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn p11_0 p11_10r := by
  refine succeed_by_split .spoke 10 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 10 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s11_step312 hred L0_1
  intro L0_2
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step260 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step314 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn p11_0 p11_7r := by
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 8 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step313 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step315 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn p11_0 p11_4r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step314 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step316 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q11_1) :
    SucceedsIn p11_0 p11_1r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s11_step315 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s11_step318 (hred : RedpartSound theRedpart) :
    SucceedsIn q11_1 p11_1l := by
  exact succeed_by_hubcap11 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f11_317

end FourColor

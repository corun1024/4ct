import FourColor.Present9Step2
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 3 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1052 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1033r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1051
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1050 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1054 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1024 p9_1024l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1053
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1052 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1055 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_922 p9_1023r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1054 hred L2_1 L2_2 L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1030 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1057 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_922 p9_1022r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1056
  intro _
  exact s9_step1055 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1063 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1022 p9_1060r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1062

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1065 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_1022 p9_1058r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 8 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1064
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step1063 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1073 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1020) :
    SucceedsIn q9_922 p9_1020r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1072
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact h9_1071 hred _
    intro _
    exact s9_step1065 hred L2_1 L2_2 L3_1 L4_1
  intro _
  exact s9_step1057 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1079 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1020 p9_1075r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1078
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1077

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1100 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1019 p9_1096r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1099
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1098

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1102 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1019 p9_1095r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1101
  intro _
  exact s9_step1100 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1104 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1019 p9_1094r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1103
  intro _
  exact s9_step1102 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1106 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1019 p9_1092r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1105
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1104 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1108 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1019 p9_1019l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1107
  intro _
  exact s9_step1106 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1109 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_922 p9_1018r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1108 hred L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact h9_1091 hred _
    intro _
    refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact h9_1085 hred _
    intro _
    exact s9_step1079 hred L2_1 L2_2 L3_1
  intro L4_1
  exact s9_step1073 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1115 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1018 p9_1111r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1114
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1113

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1117 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1018 p9_1110r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1116
  intro _
  exact s9_step1115 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1119 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1018 p9_1018l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1118
  intro _
  exact s9_step1117 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1121 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_922 p9_1016r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1120
  intro _
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact s9_step1119 hred L2_1 L2_2 L3_1
  intro _
  exact s9_step1109 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1123 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_922 p9_1015r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1122
  intro _
  exact s9_step1121 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1130 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_796 p9_921r := by
  refine succeed_by_split .hat 8 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact h9_1129 hred _
    intro _
    exact s9_step1123 hred L2_1 L2_2 L3_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1012
  intro _
  exact s9_step1011 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1156 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1152r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1155
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1154

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1158 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1150r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1157
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1156 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1160 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1147r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1159
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1158 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1162 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1146r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 5 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1161
  intro _
  exact s9_step1160 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1164 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1145r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1163
  intro _
  exact s9_step1162 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1179 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_1142 p9_1175r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1178
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1177

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1181 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_1142 p9_1173r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1180
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1179 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1183 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_1142 p9_1172r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1182
  intro _
  exact s9_step1181 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1185 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_1142 p9_1171r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1184
  intro _
  exact s9_step1183 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1187 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_1142 p9_1142l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1186
  intro _
  exact s9_step1185 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1188 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1141r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1187 hred L2_1 L2_2 L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact h9_1170 hred _
  intro _
  exact s9_step1164 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1241 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1137r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact h9_1240 hred _
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact h9_1226 hred _
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact h9_1212 hred _
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact h9_1198 hred _
  intro _
  exact s9_step1188 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1257 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917)
    (L4_1 : Successful q9_1135) :
    SucceedsIn q9_921 p9_1135r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1256
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact h9_1255 hred _
  intro _
  exact s9_step1241 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1271 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1267r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1270
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1269

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1273 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1265r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1272
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1271 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1275 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1264r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1274
  intro _
  exact s9_step1273 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1277 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1263r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1276
  intro _
  exact s9_step1275 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1279 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1262r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1278
  intro _
  exact s9_step1277 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1281 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1260r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1280
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step1279 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1283 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1259r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1282
  intro _
  exact s9_step1281 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1285 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1258r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 5 7 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1284
  intro _
  exact s9_step1283 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1287 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_1135 p9_1135l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1286
  intro _
  exact s9_step1285 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1289 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_921 p9_1133r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1288
  intro _
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1287 hred L2_1 L2_2 L3_1
  intro L4_1
  exact s9_step1257 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1291 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_921 p9_1132r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1290
  intro _
  exact s9_step1289 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1293 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_921 p9_1131r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1292
  intro _
  exact s9_step1291 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1295 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_921 p9_921l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1294
  intro _
  exact s9_step1293 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1311 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_796 p9_918r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1310
  intro _
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact h9_1309 hred _
  intro _
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1295 hred L2_1 L2_2 L3_1
  intro _
  exact s9_step1130 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1313 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794)
    (L3_1 : Successful q9_917) :
    SucceedsIn q9_796 p9_917r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1312
  intro _
  exact s9_step1311 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1338 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1334r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1337
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1336

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1340 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1332r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1339
  intro _
  exact s9_step1338 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1355 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1351r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1354
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1353

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1357 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1349r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1356
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1355 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1359 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1347r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1358
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1357 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1361 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1346r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1360
  intro _
  exact s9_step1359 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1363 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1345r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1362
  intro _
  exact s9_step1361 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1365 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1343r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1364
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1363 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1367 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1342r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1366
  intro _
  exact s9_step1365 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1369 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1331 p9_1331l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1368
  intro _
  exact s9_step1367 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1370 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1330r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1369 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1341
  intro _
  exact s9_step1340 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1373 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1328r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 0 4 7 <|
       Hubcap.two 1 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1372
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1371
  intro _
  exact s9_step1370 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1375 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1327r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1374
  intro _
  exact s9_step1373 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1377 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1326r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 4 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.two 0 2 8 <|
       Hubcap.two 0 3 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1376
  intro _
  exact s9_step1375 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1382 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1326 p9_1378r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1381
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1380

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1384 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1326 p9_1326l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 8 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1383
  intro _
  exact s9_step1382 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1386 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1324r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1385
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1384 hred L2_1 L2_2
  intro _
  exact s9_step1377 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1389 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1322r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1388
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1387
  intro _
  exact s9_step1386 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1404 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1400r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1403
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 4 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1406 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1399r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1405
  intro _
  exact s9_step1404 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1412 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1399 p9_1408r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1411
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1410

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1414 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1399 p9_1407r := by
  refine succeed_by_split .spoke 6 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1413
  intro _
  exact s9_step1412 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1416 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1399 p9_1399l := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1415
  intro _
  exact s9_step1414 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1418 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1397r := by
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1417
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s9_step1416 hred L2_1 L2_2
  intro _
  exact s9_step1406 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1420 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1395r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1419
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1418 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1422 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1394r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1421
  intro _
  exact s9_step1420 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1425 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1392r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1424
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1423
  intro _
  exact s9_step1422 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1427 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1322 p9_1391r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1426
  intro _
  exact s9_step1425 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1435 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1320r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 4 7 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1434
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact h9_1433 hred _
    intro _
    exact s9_step1427 hred L2_1 L2_2
  intro _
  exact s9_step1389 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1437 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1319r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 8 <|
       Hubcap.two 0 2 8 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 3 4 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1436
  intro _
  exact s9_step1435 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1456 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1452r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1455
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1454

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1458 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1450r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1457
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1456 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1460 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1448r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1459
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1458 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1468 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1446 p9_1464r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1467
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1466

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1470 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1446 p9_1462r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1469
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1468 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1472 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1446 p9_1446l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1471
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1470 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1474 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1444r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1473
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s9_step1472 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1460 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1476 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1443r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1475
  intro _
  exact s9_step1474 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1478 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1442r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1477
  intro _
  exact s9_step1476 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1480 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1441r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1479
  intro _
  exact s9_step1478 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1494 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1490r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1493
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1492

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1496 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1488r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1495
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1494 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1498 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1487r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1497
  intro _
  exact s9_step1496 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1501 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1485r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 7 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1500
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 6 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1499
  intro _
  exact s9_step1498 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1503 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1483r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 1 7 6 <|
       Hubcap.two 4 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1502
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1501 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1505 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1482r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1504
  intro _
  exact s9_step1503 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1508 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1440 p9_1440l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 7 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1507
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 4 2 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 7 7 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1506
  intro _
  exact s9_step1505 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1510 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1438r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1509
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1508 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1480 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1512 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_1317 p9_1317l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 7 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1511
  intro _
  exact s9_step1510 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1514 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1315r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1513
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact s9_step1512 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1437 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1516 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_1314r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1515
  intro _
  exact s9_step1514 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1518 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_917 p9_917l := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1517
  intro _
  exact s9_step1516 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1537 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L2_2 : Successful q9_794) :
    SucceedsIn q9_14 p9_795r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact h9_1536 hred _
    intro _
    refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact s9_step1518 hred L2_1 L2_2
    intro L3_1
    exact s9_step1313 hred L2_1 L2_2 L3_1
  intro L2_3
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step915 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1575 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552)
    (L3_4 : Successful q9_1566) :
    SucceedsIn q9_794 p9_1571r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1574
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1573

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1577 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552)
    (L3_4 : Successful q9_1566) :
    SucceedsIn q9_794 p9_1569r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1576
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1575 hred L2_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1579 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552)
    (L3_4 : Successful q9_1566) :
    SucceedsIn q9_794 p9_1568r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1578
  intro _
  exact s9_step1577 hred L2_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1581 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552)
    (L3_4 : Successful q9_1566) :
    SucceedsIn q9_794 p9_1567r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1580
  intro _
  exact s9_step1579 hred L2_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1587 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1566 p9_1583r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1586
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1585

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1588 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1565r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step1587 hred L2_1 L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step1581 hred L2_1 L3_1 L3_2 L3_3 L3_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1590 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1564r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1589
  intro _
  exact s9_step1588 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1592 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1563r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1591
  intro _
  exact s9_step1590 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1594 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1561r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1593
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1592 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1595 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1557r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1594 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1597 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_794 p9_1554r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1596
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1595 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1610 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1607r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_1609

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1611 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1603r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step1610 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1613 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1602r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1612
  intro _
  exact s9_step1611 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1616 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1600r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1615
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1614
  intro _
  exact s9_step1613 hred L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step1618 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q9_792)
    (L3_1 : Successful q9_1539)
    (L3_2 : Successful q9_1547)
    (L3_3 : Successful q9_1552) :
    SucceedsIn q9_1554 p9_1599r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_1617
  intro _
  exact s9_step1616 hred L2_1 L3_1 L3_2 L3_3

end FourColor

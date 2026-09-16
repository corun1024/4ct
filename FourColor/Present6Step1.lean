import FourColor.Present6Chk1
import FourColor.Present6Chk2
import FourColor.Present6Chk3
import FourColor.Present6Chk4
import FourColor.Present6Chk5
import FourColor.Present6Chk6
import FourColor.Present6Chk7
import FourColor.Present6Chk8
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 6 presentation

A chunk of the case analysis of `present6.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step26 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L0_2 : Successful q6_13)
    (L0_3 : Successful q6_19) :
    SucceedsIn p6_0 p6_22r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step27 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L0_2 : Successful q6_13)
    (L0_3 : Successful q6_19) :
    SucceedsIn p6_0 p6_19r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step26 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step29 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L0_2 : Successful q6_13) :
    SucceedsIn p6_0 p6_17r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 2 <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_28
  intro L0_3
  exact s6_step27 hred L0_1 L0_2 L0_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step30 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L0_2 : Successful q6_13) :
    SucceedsIn p6_0 p6_14r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step29 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step45 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L1_2 : Successful q6_33)
    (L1_3 : Successful q6_35)
    (L1_4 : Successful q6_37) :
    SucceedsIn q6_39 p6_39l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-2) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_44
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_43

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step46 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L1_2 : Successful q6_33)
    (L1_3 : Successful q6_35)
    (L1_4 : Successful q6_37) :
    SucceedsIn q6_13 p6_38r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact s6_step45 hred L0_1 L1_1 L1_2 L1_3 L1_4
  intro L1_5
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_41

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step48 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L1_2 : Successful q6_33)
    (L1_3 : Successful q6_35) :
    SucceedsIn q6_13 p6_36r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_47
  intro L1_4
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step46 hred L0_1 L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step53 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L1_2 : Successful q6_33) :
    SucceedsIn q6_35 p6_49r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_52
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_51

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step55 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L1_2 : Successful q6_33) :
    SucceedsIn q6_13 p6_34r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 (-1) <|
         Hubcap.two 1 3 2 <|
         Hubcap.two 2 4 (-1) <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_54
    intro _
    exact s6_step53 hred L0_1 L1_1 L1_2
  intro L1_3
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step48 hred L0_1 L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step65 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L3_1 : Successful q6_58)
    (L3_2 : Successful q6_60) :
    SucceedsIn q6_33 p6_61r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_64
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_63

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step70 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L3_1 : Successful q6_58) :
    SucceedsIn q6_60 p6_66r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-2) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_69
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_68

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step72 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31)
    (L3_1 : Successful q6_58) :
    SucceedsIn q6_33 p6_59r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 (-2) <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 2 4 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_71
    intro _
    exact s6_step70 hred L0_1 L1_1 L3_1
  intro L3_2
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step65 hred L0_1 L1_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step76 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31) :
    SucceedsIn q6_58 p6_58l := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 5 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_75
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_74

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step77 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L1_1 : Successful q6_31) :
    SucceedsIn q6_33 p6_33l := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s6_step76 hred L0_1 L1_1
  intro L3_1
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step72 hred L0_1 L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step88 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79)
    (L2_2 : Successful q6_81)
    (L2_3 : Successful q6_83) :
    SucceedsIn q6_31 p6_84r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_87
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_86

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step93 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79)
    (L2_2 : Successful q6_81) :
    SucceedsIn q6_83 p6_89r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 5 (-2) <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_92
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_91

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step95 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79)
    (L2_2 : Successful q6_81) :
    SucceedsIn q6_31 p6_82r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 2 (-1) <|
         Hubcap.two 1 5 (-1) <|
         Hubcap.two 3 4 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_94
    intro _
    exact s6_step93 hred L0_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step88 hred L0_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step100 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79) :
    SucceedsIn q6_81 p6_96r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_99
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_98

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step104 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79) :
    SucceedsIn q6_96 p6_96l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 5 (-2) <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_103
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 5 (-2) <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_102

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step105 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L2_1 : Successful q6_79) :
    SucceedsIn q6_31 p6_79r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
    · exact s6_step104 hred L0_1 L2_1
    intro _
    exact s6_step100 hred L0_1 L2_1
  intro L2_2
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step95 hred L0_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step113 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_79 p6_109r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 5 0 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_112
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_111

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step117 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_109 p6_109l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 5 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_116
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_115

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step122 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_108 p6_118r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 5 1 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_121
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_120

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step126 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_118 p6_118l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-3) <|
       Hubcap.two 1 5 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_125
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_124

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step131 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_107 p6_127r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_130
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_129

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step135 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_127 p6_127l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-3) <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_134
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_133

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step136 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_79 p6_106r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact s6_step135 hred L0_1
    intro _
    exact s6_step131 hred L0_1
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact s6_step126 hred L0_1
    intro _
    exact s6_step122 hred L0_1
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact s6_step117 hred L0_1
  intro _
  exact s6_step113 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step142 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_106 p6_138r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 5 0 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_141
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 5 0 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_140

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step148 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_137 p6_144r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_147
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 5 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_146

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step150 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_106 p6_106l := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 2 (-1) <|
         Hubcap.two 1 5 (-2) <|
         Hubcap.two 3 4 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_149
    intro _
    exact s6_step148 hred L0_1
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 5 (-1) <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_143
  intro _
  exact s6_step142 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step163 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151)
    (L3_2 : Successful q6_153)
    (L3_3 : Successful q6_155) :
    SucceedsIn q6_157 p6_157l := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 2 <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_162
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_161

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step164 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151)
    (L3_2 : Successful q6_153)
    (L3_3 : Successful q6_155) :
    SucceedsIn q6_78 p6_156r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact s6_step163 hred L0_1 L3_1 L3_2 L3_3
  intro L3_4
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L3_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_159

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step169 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151)
    (L3_2 : Successful q6_153) :
    SucceedsIn q6_155 p6_165r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-2) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_168
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step171 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151)
    (L3_2 : Successful q6_153) :
    SucceedsIn q6_78 p6_154r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 0 <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 2 4 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_170
    intro _
    exact s6_step169 hred L0_1 L3_1 L3_2
  intro L3_3
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step164 hred L0_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step178 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151) :
    SucceedsIn q6_153 p6_174r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_177
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_176

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step184 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151) :
    SucceedsIn q6_173 p6_180r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 0 <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_183
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 1 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_182

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step186 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151) :
    SucceedsIn q6_153 p6_172r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 2 <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 2 4 (-2) <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_185
    intro _
    exact s6_step184 hred L0_1 L3_1
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 1 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_179
  intro _
  exact s6_step178 hred L0_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step191 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151) :
    SucceedsIn q6_172 p6_187r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-2) <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 4 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_190
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_189

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step193 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1)
    (L3_1 : Successful q6_151) :
    SucceedsIn q6_78 p6_152r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_hubcap6 hred
          (Hubcap.two 0 5 0 <|
           Hubcap.two 1 3 1 <|
           Hubcap.two 2 4 (-1) <|
           Hubcap.nil)
          rfl (by decide +kernel) (by decide +kernel) f6_192
      intro _
      exact s6_step191 hred L0_1 L3_1
    intro _
    exact s6_step186 hred L0_1 L3_1
  intro L3_2
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step171 hred L0_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step200 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_151 p6_196r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_199
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_198

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step206 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_195 p6_202r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 2 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_205
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 0 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_204

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step208 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_151 p6_194r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 1 <|
         Hubcap.two 1 3 (-2) <|
         Hubcap.two 2 4 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_207
    intro _
    exact s6_step206 hred L0_1
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 1 <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 2 4 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_201
  intro _
  exact s6_step200 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step210 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_78 p6_78l := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 0 <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 2 4 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_209
    intro _
    exact s6_step208 hred L0_1
  intro L3_1
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step193 hred L0_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step211 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn q6_13 p6_13l := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact s6_step210 hred L0_1
    intro _
    refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
      · exact s6_step150 hred L0_1
      intro _
      exact s6_step136 hred L0_1
    intro L2_1
    exact s6_step105 hred L0_1 L2_1
  intro L1_1
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact s6_step77 hred L0_1 L1_1
  intro L1_2
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 0 true L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step55 hred L0_1 L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step212 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn p6_0 p6_10r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s6_step211 hred L0_1
  intro L0_2
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step30 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step213 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn p6_0 p6_6r := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s6_step212 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step214 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q6_1) :
    SucceedsIn p6_0 p6_3r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step213 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step238 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L1_7 : Successful q6_229)
    (L1_8 : Successful q6_231) :
    SucceedsIn q6_1 p6_234r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_237
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_236

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step242 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L1_7 : Successful q6_229)
    (L1_8 : Successful q6_231) :
    SucceedsIn q6_234 p6_234l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_241
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_240

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step244 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L1_7 : Successful q6_229)
    (L1_8 : Successful q6_231) :
    SucceedsIn q6_1 p6_231r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_8
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_243
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step242 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8
  intro _
  exact s6_step238 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step248 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L1_7 : Successful q6_229) :
    SucceedsIn q6_231 p6_231l := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_247
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_246

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step257 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_229 p6_253r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_256
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_255

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step261 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_253 p6_253l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_260
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_259

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step266 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_251 p6_251l := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_265
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_264

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step267 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_229 p6_250r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact s6_step266 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_262
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step261 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro _
  exact s6_step257 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step272 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_250 p6_268r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_271
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_270

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step276 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_268 p6_268l := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_275
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_274

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step285 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L3_1 : Successful q6_277) :
    SucceedsIn q6_249 p6_281r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_284
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step289 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L3_1 : Successful q6_277) :
    SucceedsIn q6_281 p6_281l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_288
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_287

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step292 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227)
    (L3_1 : Successful q6_277) :
    SucceedsIn q6_249 p6_278r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_291
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_290
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step289 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L3_1
  intro _
  exact s6_step285 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step294 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_249 p6_249l := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_293
  intro L3_1
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step292 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step295 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225)
    (L1_6 : Successful q6_227) :
    SucceedsIn q6_1 p6_228r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact s6_step294 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
    intro _
    refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
      · exact s6_step276 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
      intro _
      exact s6_step272 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
    intro _
    exact s6_step267 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6
  intro L1_7
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_7
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact s6_step248 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7
  intro L1_8
  exact s6_step244 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6 L1_7 L1_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step304 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_227 p6_300r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 1 2 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_303
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_302

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step307 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_227 p6_297r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 1 2 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_306
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 1 2 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_305
  intro _
  exact s6_step304 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_297 p6_310r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_313
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-3) <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_312

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step317 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_297 p6_297l := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_316
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_315
  intro _
  exact s6_step314 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step321 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_296 p6_296l := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 1 2 0 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_320
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_319

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step322 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222)
    (L1_5 : Successful q6_225) :
    SucceedsIn q6_1 p6_226r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
    · exact s6_step321 hred L1_1 L1_2 L1_3 L1_4 L1_5
    intro _
    refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact s6_step317 hred L1_1 L1_2 L1_3 L1_4 L1_5
    intro _
    exact s6_step307 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro L1_6
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step295 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step330 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222) :
    SucceedsIn q6_225 p6_326r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_329
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-1) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_328

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step337 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222) :
    SucceedsIn q6_324 p6_333r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 4 5 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_336
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 0 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_335

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step339 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222) :
    SucceedsIn q6_225 p6_323r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 2 0 <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 4 5 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_338
    intro _
    exact s6_step337 hred L1_1 L1_2 L1_3 L1_4
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_331
  intro _
  exact s6_step330 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step341 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222) :
    SucceedsIn q6_1 p6_224r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 2 (-1) <|
         Hubcap.two 1 3 (-1) <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_340
    intro _
    exact s6_step339 hred L1_1 L1_2 L1_3 L1_4
  intro L1_5
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step322 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step345 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220)
    (L1_4 : Successful q6_222) :
    SucceedsIn q6_224 p6_224l := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_344
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 5 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_343

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step351 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220) :
    SucceedsIn q6_222 p6_347r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 5 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 2 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_350
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 1 <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_349

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step353 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218)
    (L1_3 : Successful q6_220) :
    SucceedsIn q6_1 p6_221r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 5 (-2) <|
         Hubcap.two 1 3 1 <|
         Hubcap.two 2 4 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_352
    intro _
    exact s6_step351 hred L1_1 L1_2 L1_3
  intro L1_4
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact s6_step345 hred L1_1 L1_2 L1_3 L1_4
  intro _
  exact s6_step341 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step366 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218) :
    SucceedsIn q6_220 p6_362r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_365
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_364

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step369 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218) :
    SucceedsIn q6_220 p6_359r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_368
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_367
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s6_step366 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step372 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218) :
    SucceedsIn q6_220 p6_357r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 0 <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 4 5 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_371
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_370
  intro _
  exact s6_step369 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step373 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L1_2 : Successful q6_218) :
    SucceedsIn q6_220 p6_220l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s6_step372 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step391 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382)
    (L2_5 : Successful q6_384) :
    SucceedsIn q6_218 p6_387r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_390
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_389

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step395 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382)
    (L2_5 : Successful q6_384) :
    SucceedsIn q6_387 p6_387l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_394
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_393

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step397 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382)
    (L2_5 : Successful q6_384) :
    SucceedsIn q6_218 p6_384r := by
  refine succeed_by_split .fan1 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_396
  intro _
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact s6_step395 hred L1_1 L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s6_step391 hred L1_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step404 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382) :
    SucceedsIn q6_384 p6_400r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 1 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_403
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-3) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_402

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step408 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382) :
    SucceedsIn q6_400 p6_400l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_407
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_406

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step415 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382) :
    SucceedsIn q6_398 p6_411r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_414
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_413

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step419 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382) :
    SucceedsIn q6_411 p6_411l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_418
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_417

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step421 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379)
    (L2_4 : Successful q6_382) :
    SucceedsIn q6_384 p6_384l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 4 0 <|
         Hubcap.two 3 5 0 <|
         Hubcap.two 1 2 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_420
    intro _
    refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
    · exact s6_step419 hred L1_1 L2_1 L2_2 L2_3 L2_4
    intro _
    exact s6_step415 hred L1_1 L2_1 L2_2 L2_3 L2_4
  intro _
  refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_409
  intro _
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact s6_step408 hred L1_1 L2_1 L2_2 L2_3 L2_4
  intro _
  exact s6_step404 hred L1_1 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step428 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_382 p6_424r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_427
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_426

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step433 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_423 p6_423l := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 1 2 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_432
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_431

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step434 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_382 p6_382l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact s6_step433 hred L1_1 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_429
  intro _
  exact s6_step428 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step442 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_381 p6_438r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_441
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_440

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step445 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_381 p6_436r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_444
  intro _
  refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_443
  intro _
  exact s6_step442 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step449 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_436 p6_436l := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 2 <|
       Hubcap.two 1 2 (-2) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_448
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_447

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step454 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_435 p6_450r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 3 5 1 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_453
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_452

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step456 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_381 p6_381l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 4 (-1) <|
         Hubcap.two 3 5 2 <|
         Hubcap.two 1 2 (-1) <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_455
    intro _
    exact s6_step454 hred L1_1 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact s6_step449 hred L1_1 L2_1 L2_2 L2_3
  intro _
  exact s6_step445 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step457 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377)
    (L2_3 : Successful q6_379) :
    SucceedsIn q6_218 p6_380r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s6_step456 hred L1_1 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step434 hred L1_1 L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 6 false (by decide +kernel) ?_ ?_
  · exact s6_step421 hred L1_1 L2_1 L2_2 L2_3 L2_4
  intro L2_5
  exact s6_step397 hred L1_1 L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step463 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377) :
    SucceedsIn q6_379 p6_459r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_462
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_461

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step467 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377) :
    SucceedsIn q6_459 p6_459l := by
  refine succeed_by_split .fan1 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 1 <|
       Hubcap.two 1 2 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_466
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_465

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step469 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375)
    (L2_2 : Successful q6_377) :
    SucceedsIn q6_218 p6_378r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 4 0 <|
         Hubcap.two 1 2 0 <|
         Hubcap.two 3 5 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_468
    intro _
    refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact s6_step467 hred L1_1 L2_1 L2_2
    intro _
    exact s6_step463 hred L1_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step457 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step474 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375) :
    SucceedsIn q6_377 p6_470r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_473
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 3 1 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 0 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_472

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step476 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_375) :
    SucceedsIn q6_218 p6_376r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 1 (-2) <|
         Hubcap.two 2 4 1 <|
         Hubcap.two 3 5 1 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_475
    intro _
    exact s6_step474 hred L1_1 L2_1
  intro L2_2
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step469 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step482 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_375 p6_478r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 2 4 1 <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 0 5 (-1) <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_481
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 2 4 1 <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 0 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_480

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_218 p6_374r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s6_step482 hred L1_1
  intro L2_1
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step476 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step484 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_1 p6_217r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s6_step483 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact s6_step373 hred L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step353 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step501 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487)
    (L2_2 : Successful q6_493)
    (L2_3 : Successful q6_495) :
    SucceedsIn q6_217 p6_496r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_500
  intro L2_4
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_499

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step506 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487)
    (L2_2 : Successful q6_493) :
    SucceedsIn q6_495 p6_502r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_505
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_504

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step508 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487)
    (L2_2 : Successful q6_493) :
    SucceedsIn q6_217 p6_494r := by
  refine succeed_by_split .fan1 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 4 0 <|
         Hubcap.two 3 5 0 <|
         Hubcap.two 1 2 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_507
    intro _
    exact s6_step506 hred L1_1 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .fan1 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step501 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step512 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487) :
    SucceedsIn q6_493 p6_493l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_511
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_510

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step517 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487) :
    SucceedsIn q6_492 p6_492l := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 3 5 (-1) <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_516
  intro L3_1
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_515

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step519 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487) :
    SucceedsIn q6_217 p6_490r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.two 1 2 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_518
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s6_step517 hred L1_1 L2_1
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact s6_step512 hred L1_1 L2_1
  intro L2_2
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step508 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step520 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L2_1 : Successful q6_487) :
    SucceedsIn q6_217 p6_487r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step519 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step529 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_487 p6_525r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 3 5 (-1) <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_528
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_527

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step534 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_524 p6_524l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-3) <|
       Hubcap.two 3 5 (-2) <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_533
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_532

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step540 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_523 p6_536r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_539
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_538

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step545 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_535 p6_535l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-3) <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_544
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-4) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_543

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step546 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_487 p6_522r := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact s6_step545 hred L1_1
    intro _
    refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 2 (-2) <|
         Hubcap.two 1 3 0 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_541
    intro _
    exact s6_step540 hred L1_1
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s6_step534 hred L1_1
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-1) <|
       Hubcap.two 3 5 (-1) <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_530
  intro _
  exact s6_step529 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step554 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_549 p6_549l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-2) <|
       Hubcap.two 1 3 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_553
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_552

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step558 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_548 p6_548l := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-3) <|
       Hubcap.two 1 3 (-1) <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_557
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_556

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step562 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_547 p6_547l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-4) <|
       Hubcap.two 1 3 (-2) <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_561
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-1) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_560

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step563 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_522 p6_522l := by
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step562 hred L1_1
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step558 hred L1_1
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact s6_step554 hred L1_1
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_550

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step569 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215)
    (L4_1 : Successful q6_564) :
    SucceedsIn q6_521 p6_565r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-3) <|
       Hubcap.two 3 5 (-3) <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_568
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_567

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step574 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_564 p6_570r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 4 (-2) <|
       Hubcap.two 3 5 (-4) <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_573
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-3) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_572

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step578 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_570 p6_570l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 2 (-3) <|
       Hubcap.two 1 3 (-3) <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_577
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_576

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step579 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_487 p6_487l := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
      · exact s6_step578 hred L1_1
      intro _
      exact s6_step574 hred L1_1
    intro L4_1
    refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 2 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s6_step569 hred L1_1 L4_1
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact s6_step563 hred L1_1
  intro _
  exact s6_step546 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step580 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q6_215) :
    SucceedsIn q6_1 p6_216r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 1 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact s6_step579 hred L1_1
    intro L2_1
    exact s6_step520 hred L1_1 L2_1
  intro _
  exact s6_step484 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step595 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_215 p6_591r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_594
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_593

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step599 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_591 p6_591l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_598
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_597

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step605 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_589 p6_601r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_604
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_603

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step607 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_215 p6_588r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 1 0 <|
         Hubcap.two 2 4 0 <|
         Hubcap.two 3 5 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_606
    intro _
    exact s6_step605 hred L3_1 L3_2
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_600
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step599 hred L3_1 L3_2
  intro _
  exact s6_step595 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step613 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_587 p6_587l := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_612
  intro L4_1
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 1 2 0 <|
     Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_611

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step614 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583)
    (L3_2 : Successful q6_585) :
    SucceedsIn q6_215 p6_585r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact s6_step613 hred L3_1 L3_2
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_608
  intro _
  exact s6_step607 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step619 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_583) :
    SucceedsIn q6_585 p6_615r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 1 2 0 <|
       Hubcap.two 0 4 (-1) <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_618
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 1 2 1 <|
     Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_617

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step625 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_583 p6_621r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-2) <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_624
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_623

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step629 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_621 p6_621l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_628
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_627

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step633 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_620 p6_620l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_632
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_631

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step634 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_215 p6_582r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s6_step633 hred
    intro _
    refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · exact s6_step629 hred
    intro _
    exact s6_step625 hred
  intro L3_1
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s6_step619 hred L3_1
  intro L3_2
  exact s6_step614 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step639 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_582 p6_635r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-3) <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_638
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-4) <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_637

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step643 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_635 p6_635l := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 1 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_642
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_641

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step657 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_581 p6_653r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_656
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_655

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step661 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_653 p6_653l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-2) <|
       Hubcap.two 2 4 2 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_660
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_659

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step667 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_651 p6_663r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-2) <|
       Hubcap.two 2 4 2 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_666
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_665

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step669 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_581 p6_650r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap6 hred
        (Hubcap.two 0 1 (-1) <|
         Hubcap.two 2 4 1 <|
         Hubcap.two 3 5 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f6_668
    intro _
    exact s6_step667 hred L3_1 L3_2
  intro _
  refine succeed_by_split .fan1 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_662
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact s6_step661 hred L3_1 L3_2
  intro _
  exact s6_step657 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step675 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_649 p6_649l := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 (-1) <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_674
  intro L4_1
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 1 2 (-1) <|
     Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_673

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step676 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645)
    (L3_2 : Successful q6_647) :
    SucceedsIn q6_581 p6_647r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact s6_step675 hred L3_1 L3_2
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_670
  intro _
  exact s6_step669 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step681 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q6_645) :
    SucceedsIn q6_647 p6_677r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 1 2 (-1) <|
       Hubcap.two 0 4 0 <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_680
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 1 2 0 <|
     Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_679

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step687 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_645 p6_683r := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 (-1) <|
       Hubcap.two 3 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_686
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_685

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step691 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_683 p6_683l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_690
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_689

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step695 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_682 p6_682l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_694
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_693

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step696 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_581 p6_644r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s6_step695 hred
    intro _
    refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · exact s6_step691 hred
    intro _
    exact s6_step687 hred
  intro L3_1
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s6_step681 hred L3_1
  intro L3_2
  exact s6_step676 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step701 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_644 p6_697r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 (-2) <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_700
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 (-3) <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_699

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step705 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_697 p6_697l := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap6 hred
      (Hubcap.two 0 1 0 <|
       Hubcap.two 2 4 0 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f6_704
  intro _
  exact succeed_by_hubcap6 hred
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f6_703

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step706 (hred : RedpartSound theRedpart) :
    SucceedsIn q6_215 p6_215l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
      · exact s6_step705 hred
      intro _
      exact s6_step701 hred
    intro _
    exact s6_step696 hred
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · exact s6_step643 hred
    intro _
    exact s6_step639 hred
  intro _
  exact s6_step634 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s6_step707 (hred : RedpartSound theRedpart) :
    SucceedsIn p6_0 p6_0 := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact s6_step706 hred
    intro L1_1
    refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s6_step580 hred L1_1
  intro L0_1
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s6_step214 hred L0_1

end FourColor

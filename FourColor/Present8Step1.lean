import FourColor.Present8Hub5
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 1 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step44 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_40r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_43
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_42

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step46 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_38r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_45
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step44 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step48 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_36r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_47
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step46 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step51 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_34r := by
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_50
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_49
  intro _
  exact s8_step48 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step54 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_32r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_53
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_52
  intro _
  exact s8_step51 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step55 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_29r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step54 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step56 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1)
    (L0_2 : Successful q8_25) :
    SucceedsIn p8_0 p8_26r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step55 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step71 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_67r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_70
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_69

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step73 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_66r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_72
  intro _
  exact s8_step71 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step76 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_64r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_75
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_74
  intro _
  exact s8_step73 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step79 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_62r := by
  refine succeed_by_split .spoke 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_78
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_77
  intro _
  exact s8_step76 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step81 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_61r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 0 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_80
  intro _
  exact s8_step79 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step84 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_59r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_83
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 6 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_82
  intro _
  exact s8_step81 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step87 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn q8_25 p8_57r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_86
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_85
  intro _
  exact s8_step84 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step89 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_24r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 4 <|
         Hubcap.two 4 5 6 <|
         Hubcap.two 6 7 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_88
    intro _
    exact s8_step87 hred L0_1
  intro L0_2
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L0_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step56 hred L0_1 L0_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step92 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_22r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 7 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_91
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_90
  intro _
  exact s8_step89 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step95 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_20r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 7 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_94
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_93
  intro _
  exact s8_step92 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step98 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_18r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 7 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_97
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_96
  intro _
  exact s8_step95 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step101 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_16r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 7 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_100
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_99
  intro _
  exact s8_step98 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step104 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_14r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_103
  intro _
  refine succeed_by_split .spoke 7 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 0 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_102
  intro _
  exact s8_step101 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step107 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_12r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_106
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_105
  intro _
  exact s8_step104 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step110 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_10r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_109
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_108
  intro _
  exact s8_step107 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step113 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_8r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_112
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_111
  intro _
  exact s8_step110 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step114 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_5r := by
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
  exact s8_step113 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step115 (hred : RedpartSound theRedpart)
    (L0_1 : Successful q8_1) :
    SucceedsIn p8_0 p8_2r := by
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
  exact s8_step114 hred L0_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step151 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_147r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_150
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_149

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step153 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_145r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_152
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step151 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step155 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_143r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_154
  intro _
  exact s8_step153 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step158 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_141r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_157
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_156
  intro _
  exact s8_step155 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step161 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_139r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_160
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_159
  intro _
  exact s8_step158 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step164 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L1_6 : Successful q8_136) :
    SucceedsIn q8_1 p8_137r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_163
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_162
  intro _
  exact s8_step161 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step173 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_136 p8_169r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_172
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_171

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step191 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_187r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_190
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_189

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step193 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_185r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_192
  intro _
  refine succeed_by_split .fan1 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step191 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step195 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_184r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_194
  intro _
  exact s8_step193 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step197 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_183r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_196
  intro _
  exact s8_step195 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step199 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_182r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_198
  intro _
  exact s8_step197 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step202 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_180r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_201
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_200
  intro _
  exact s8_step199 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step204 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_178r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_203
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step202 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step207 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_176r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_206
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_205
  intro _
  exact s8_step204 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step210 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_168 p8_174r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_209
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_208
  intro _
  exact s8_step207 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step212 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_136 p8_167r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.two 0 1 6 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 4 7 6 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_211
    intro _
    exact s8_step210 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step173 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step215 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_136 p8_165r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_214
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_213
  intro _
  exact s8_step212 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step217 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_1 p8_135r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 2 0 <|
         Hubcap.two 1 7 7 <|
         Hubcap.two 3 4 4 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_216
    intro _
    exact s8_step215 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro L1_6
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L1_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step164 hred L1_1 L1_2 L1_3 L1_4 L1_5 L1_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step240 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220)
    (L2_2 : Successful q8_228) :
    SucceedsIn q8_135 p8_236r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_239
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_238

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step242 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220)
    (L2_2 : Successful q8_228) :
    SucceedsIn q8_135 p8_233r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_241
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step240 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step244 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220)
    (L2_2 : Successful q8_228) :
    SucceedsIn q8_135 p8_229r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_243
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step242 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step248 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220) :
    SucceedsIn q8_228 p8_228l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_247
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_246

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step250 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220) :
    SucceedsIn q8_135 p8_226r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_249
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s8_step248 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1
  intro L2_2
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step244 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step253 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220) :
    SucceedsIn q8_135 p8_224r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_252
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_251
  intro _
  exact s8_step250 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step255 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131)
    (L2_1 : Successful q8_220) :
    SucceedsIn q8_135 p8_222r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_254
  intro _
  exact s8_step253 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step267 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_263r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_266
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_265

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step270 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_261r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_269
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 4 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_268
  intro _
  exact s8_step267 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step273 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_259r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_272
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_271
  intro _
  exact s8_step270 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step275 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_258r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_274
  intro _
  exact s8_step273 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step277 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_257r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_276
  intro _
  exact s8_step275 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step279 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_256r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_278
  intro _
  exact s8_step277 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step281 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_220 p8_220l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_280
  intro _
  exact s8_step279 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step283 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_135 p8_218r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_282
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s8_step281 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro L2_1
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step255 hred L1_1 L1_2 L1_3 L1_4 L1_5 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step285 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_1 p8_134r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 3 4 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 4 7 5 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_284
    intro _
    exact s8_step283 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  exact s8_step217 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step295 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_134 p8_291r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 3 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_294
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_293

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step298 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_134 p8_289r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_297
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_296
  intro _
  exact s8_step295 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step300 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_134 p8_287r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_299
  intro _
  exact s8_step298 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step303 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_134 p8_134l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_302
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 6 <|
       Hubcap.two 2 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_301
  intro _
  exact s8_step300 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step305 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127)
    (L1_5 : Successful q8_131) :
    SucceedsIn q8_1 p8_132r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_304
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact s8_step303 hred L1_1 L1_2 L1_3 L1_4 L1_5
  intro _
  exact s8_step285 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step326 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_322r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_325
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_324

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_320r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_328
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_327
  intro _
  exact s8_step326 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step331 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_318r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_330
  intro _
  exact s8_step329 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step334 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_316r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_333
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_332
  intro _
  exact s8_step331 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step347 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_343r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_346
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_345

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step349 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_342r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_348
  intro _
  exact s8_step347 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step351 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_341r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_350
  intro _
  exact s8_step349 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step353 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_340r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_352
  intro _
  exact s8_step351 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step355 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_338r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_354
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step353 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step358 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_336r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_357
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_356
  intro _
  exact s8_step355 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step361 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_316 p8_316l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_360
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_359
  intro _
  exact s8_step358 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step363 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_314r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_362
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step361 hred L1_1 L1_2 L1_3 L1_4
  intro _
  exact s8_step334 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step365 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_312r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_364
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step363 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step367 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_311r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_366
  intro _
  exact s8_step365 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step370 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_309r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_369
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_368
  intro _
  exact s8_step367 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step393 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_389r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_392
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_391

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step395 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_388r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_394
  intro _
  exact s8_step393 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step398 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_386r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_397
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_396
  intro _
  exact s8_step395 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step400 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_384r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_399
  intro _
  exact s8_step398 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step403 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_382r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_402
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 6 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_401
  intro _
  exact s8_step400 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step406 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_380r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_405
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_404
  intro _
  exact s8_step403 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step416 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_379 p8_412r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_415
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_414

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step419 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_379 p8_410r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 7 3 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_418
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_417
  intro _
  exact s8_step416 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step421 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_379 p8_409r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_420
  intro _
  exact s8_step419 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step424 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_379 p8_379l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_423
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_422
  intro _
  exact s8_step421 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step425 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_378r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step424 hred L1_1 L1_2 L1_3 L1_4
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_407
  intro _
  exact s8_step406 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step427 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_376r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_426
  intro _
  exact s8_step425 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step430 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_374r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_429
  intro _
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_428
  intro _
  exact s8_step427 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step433 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_308 p8_372r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_432
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_431
  intro _
  exact s8_step430 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step435 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_307r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 7 3 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 3 4 4 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_434
    intro _
    exact s8_step433 hred L1_1 L1_2 L1_3 L1_4
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_371
  intro _
  exact s8_step370 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step438 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_131 p8_131l := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_437
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_436
  intro _
  exact s8_step435 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step440 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_1 p8_129r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_439
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step438 hred L1_1 L1_2 L1_3 L1_4
  intro L1_5
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L1_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step305 hred L1_1 L1_2 L1_3 L1_4 L1_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step442 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L1_4 : Successful q8_127) :
    SucceedsIn q8_1 p8_127r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L1_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_441
  intro _
  exact s8_step440 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step466 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_462r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 4 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_465
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_464

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step469 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_460r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_468
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 4 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_467
  intro _
  exact s8_step466 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step471 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_458r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_470
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step469 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step474 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_456r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_473
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 3 7 5 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_472
  intro _
  exact s8_step471 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step477 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_454r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_476
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_475
  intro _
  exact s8_step474 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step480 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_452r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_479
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_478
  intro _
  exact s8_step477 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step500 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_496r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_499
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_498

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step502 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_494r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_501
  intro _
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step500 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step504 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_492r := by
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_503
  intro _
  exact s8_step502 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step506 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_490r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_505
  intro _
  exact s8_step504 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step508 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_488r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_507
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step506 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step511 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_486r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_510
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_509
  intro _
  exact s8_step508 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step514 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_484r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_513
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_512
  intro _
  exact s8_step511 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step517 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_451 p8_482r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 2 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_516
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_515
  intro _
  exact s8_step514 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step519 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_450r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 7 4 <|
         Hubcap.two 3 4 3 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_518
    intro _
    exact s8_step517 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_481
  intro _
  exact s8_step480 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step522 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_448r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_521
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_520
  intro _
  exact s8_step519 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step525 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_446r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_524
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_523
  intro _
  exact s8_step522 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step538 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_534r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_537
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_536

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step541 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_532r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_540
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_539
  intro _
  exact s8_step538 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step544 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_530r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_543
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_542
  intro _
  exact s8_step541 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step546 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_529r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_545
  intro _
  exact s8_step544 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step549 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_527r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_548
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_547
  intro _
  exact s8_step546 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step551 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_526r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_550
  intro _
  exact s8_step549 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step553 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_446 p8_446l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_552
  intro _
  exact s8_step551 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step555 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_444r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_554
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step553 hred L1_1 L1_2 L1_3
  intro _
  exact s8_step525 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step558 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_127 p8_127l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_557
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_556
  intro _
  exact s8_step555 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step560 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_1 p8_125r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_559
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step558 hred L1_1 L1_2 L1_3
  intro L1_4
  exact s8_step442 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step563 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_1 p8_123r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_562
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 7 7 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_561
  intro _
  exact s8_step560 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step584 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565)
    (L2_2 : Successful q8_575) :
    SucceedsIn q8_122 p8_581r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_583

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step585 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565)
    (L2_2 : Successful q8_575) :
    SucceedsIn q8_122 p8_577r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step584 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step592 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_575 p8_588r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_591
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_590

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step594 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_575 p8_586r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_593
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step592 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step596 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_575 p8_575l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_595
  intro _
  exact s8_step594 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step598 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_122 p8_573r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_597
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step596 hred L1_1 L1_2 L1_3 L2_1
  intro L2_2
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step585 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step601 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_122 p8_571r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_600
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_599
  intro _
  exact s8_step598 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step604 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_122 p8_569r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_603
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_602
  intro _
  exact s8_step601 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step606 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L2_1 : Successful q8_565) :
    SucceedsIn q8_122 p8_567r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_605
  intro _
  exact s8_step604 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step631 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_627r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_630
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_629

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step633 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_626r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_632
  intro _
  exact s8_step631 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step635 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_624r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_634
  intro _
  exact s8_step633 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step637 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_623r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_636
  intro _
  exact s8_step635 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step639 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_620r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_638
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step637 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step642 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_618r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_641
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_640
  intro _
  exact s8_step639 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step645 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_616r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_644
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_643
  intro _
  exact s8_step642 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step648 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_614r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 7 5 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_647
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 7 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_646
  intro _
  exact s8_step645 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step654 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_614 p8_651r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_653

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step655 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_613r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 1 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step654 hred L1_1 L1_2 L1_3 L3_1
  intro _
  exact s8_step648 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step658 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120)
    (L3_1 : Successful q8_611) :
    SucceedsIn q8_565 p8_611r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.two 4 7 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_657
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 7 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_656
  intro _
  exact s8_step655 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step673 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_669r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_672
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_671

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step676 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_667r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_675
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_674
  intro _
  exact s8_step673 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step679 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_665r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_678
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_677
  intro _
  exact s8_step676 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step682 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_663r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_681
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_680
  intro _
  exact s8_step679 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step693 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_663 p8_689r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_692
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_691

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step696 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_663 p8_687r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_695
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_694
  intro _
  exact s8_step693 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step698 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_663 p8_686r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_697
  intro _
  exact s8_step696 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step700 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_663 p8_684r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_699
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step698 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step702 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_663 p8_663l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_701
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step700 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step704 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_661r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 4 <|
       Hubcap.two 2 7 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_703
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact s8_step702 hred L1_1 L1_2 L1_3
  intro _
  exact s8_step682 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step712 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_661 p8_708r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_711
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_710

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step715 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_661 p8_706r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_714
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_713
  intro _
  exact s8_step712 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step717 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_661 p8_705r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_716
  intro _
  exact s8_step715 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step719 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_660r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 3 2 <|
         Hubcap.one 6 3 <|
         Hubcap.two 0 1 6 <|
         Hubcap.two 2 7 6 <|
         Hubcap.two 4 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_718
    intro _
    exact s8_step717 hred L1_1 L1_2 L1_3
  intro _
  exact s8_step704 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step722 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_611 p8_611l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_721
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_720
  intro _
  exact s8_step719 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step724 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_565 p8_609r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_723
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step722 hred L1_1 L1_2 L1_3
  intro L3_1
  exact s8_step658 hred L1_1 L1_2 L1_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step727 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_565 p8_607r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_726
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_725
  intro _
  exact s8_step724 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step729 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_122 p8_122l := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 1 2 <|
         Hubcap.one 2 3 <|
         Hubcap.one 3 3 <|
         Hubcap.two 4 7 6 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_728
    intro _
    exact s8_step727 hred L1_1 L1_2 L1_3
  intro L2_1
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step606 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step730 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L1_3 : Successful q8_120) :
    SucceedsIn q8_1 p8_121r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact s8_step729 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_564
  intro _
  exact s8_step563 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step752 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740)
    (L2_3 : Successful q8_746) :
    SucceedsIn q8_120 p8_748r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_751
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_750

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step754 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740)
    (L2_3 : Successful q8_746) :
    SucceedsIn q8_120 p8_746r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_753
  intro _
  exact s8_step752 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step761 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_746 p8_757r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_760
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_759

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step763 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_746 p8_756r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_762
  intro _
  exact s8_step761 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step766 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_746 p8_746l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_765
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_764
  intro _
  exact s8_step763 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step775 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_745 p8_771r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_774
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_773

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step778 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_745 p8_769r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_777
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_776
  intro _
  exact s8_step775 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step780 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_745 p8_767r := by
  refine succeed_by_split .fan1 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_779
  intro _
  exact s8_step778 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step789 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_744 p8_785r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_788
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_787

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step791 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_744 p8_784r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_790
  intro _
  exact s8_step789 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step794 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_744 p8_782r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_793
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_792
  intro _
  exact s8_step791 hred L1_1 L1_2 L2_1 L2_2

end FourColor

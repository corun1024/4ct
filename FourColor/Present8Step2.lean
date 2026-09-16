import FourColor.Present8Step1
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 2 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step795 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_120 p8_743r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step794 hred L1_1 L1_2 L2_1 L2_2
  intro _
  refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step780 hred L1_1 L1_2 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step766 hred L1_1 L1_2 L2_1 L2_2
  intro L2_3
  exact s8_step754 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step801 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_743 p8_797r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_800
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_799

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step812 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_796 p8_808r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_811
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_810

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step814 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_743 p8_743l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 2 <|
         Hubcap.one 6 4 <|
         Hubcap.one 7 2 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 4 5 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_813
    intro _
    exact s8_step812 hred L1_1 L1_2 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact h8_807 hred _
  intro _
  exact s8_step801 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step832 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740)
    (L3_1 : Successful q8_821) :
    SucceedsIn q8_742 p8_828r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_831
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_830

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step834 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740)
    (L3_1 : Successful q8_821) :
    SucceedsIn q8_742 p8_825r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_833
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step832 hred L1_1 L1_2 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step835 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740)
    (L3_1 : Successful q8_821) :
    SucceedsIn q8_742 p8_821r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step834 hred L1_1 L1_2 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step849 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_845r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_848
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_847

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step851 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_844r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_850
  intro _
  exact s8_step849 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step853 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_843r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_852
  intro _
  exact s8_step851 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step855 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_842r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_854
  intro _
  exact s8_step853 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step857 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_841r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_856
  intro _
  exact s8_step855 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step859 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_837r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_858
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step857 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step861 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_836r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_860
  intro _
  exact s8_step859 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step863 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_821 p8_821l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_862
  intro _
  exact s8_step861 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step865 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_742 p8_819r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 4 6 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_864
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step863 hred L1_1 L1_2 L2_1 L2_2
  intro L3_1
  exact s8_step835 hred L1_1 L1_2 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step873 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_819 p8_869r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_872
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_871

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step875 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_819 p8_867r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_874
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step873 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step877 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_742 p8_817r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_876
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step875 hred L1_1 L1_2 L2_1 L2_2
  intro _
  exact s8_step865 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step880 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_742 p8_815r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_879
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_878
  intro _
  exact s8_step877 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step882 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L2_2 : Successful q8_740) :
    SucceedsIn q8_742 p8_742l := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 5 7 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_881
  intro _
  exact s8_step880 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step900 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_896r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_899
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_898

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step902 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_894r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_901
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step900 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step904 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_893r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_903
  intro _
  exact s8_step902 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step906 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_891r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_905
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step904 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step908 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_890r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_907
  intro _
  exact s8_step906 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step910 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_889r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_909
  intro _
  exact s8_step908 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step921 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_917r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_920
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_919

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step924 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_915r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_923
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_922
  intro _
  exact s8_step921 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step926 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_914r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_925
  intro _
  exact s8_step924 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step928 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_913r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_927
  intro _
  exact s8_step926 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step930 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_912r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_929
  intro _
  exact s8_step928 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step932 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_888 p8_911r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_931
  intro _
  exact s8_step930 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step934 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_887r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 5 3 <|
         Hubcap.one 6 3 <|
         Hubcap.one 7 2 <|
         Hubcap.two 1 2 4 <|
         Hubcap.two 3 4 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_933
    intro _
    exact s8_step932 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step910 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step944 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_887 p8_939r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_943
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_942

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step946 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_887 p8_938r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_945
  intro _
  exact s8_step944 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step949 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_887 p8_936r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_948
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_947
  intro _
  exact s8_step946 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step952 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_887 p8_887l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_951
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_950
  intro _
  exact s8_step949 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step963 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_886 p8_959r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_962
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_961

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step966 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_886 p8_957r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 3 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_965
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_964
  intro _
  exact s8_step963 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step968 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_886 p8_956r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_967
  intro _
  exact s8_step966 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step970 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_886 p8_955r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_969
  intro _
  exact s8_step968 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step972 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_886 p8_953r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_971
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step970 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step974 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_885r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 1 0 <|
         Hubcap.one 5 3 <|
         Hubcap.one 6 3 <|
         Hubcap.one 7 2 <|
         Hubcap.two 0 2 7 <|
         Hubcap.two 3 4 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_973
    intro _
    exact s8_step972 hred L1_1 L1_2 L2_1
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step952 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step934 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step977 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_740 p8_883r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_976
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_975
  intro _
  exact s8_step974 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step990 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_980) :
    SucceedsIn q8_883 p8_986r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_989
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_988

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step992 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_980) :
    SucceedsIn q8_883 p8_985r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_991
  intro _
  exact s8_step990 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step994 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_980) :
    SucceedsIn q8_883 p8_984r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_993
  intro _
  exact s8_step992 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step997 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_980) :
    SucceedsIn q8_883 p8_982r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_996
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_995
  intro _
  exact s8_step994 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step999 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_980) :
    SucceedsIn q8_883 p8_980r := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_998
  intro _
  exact s8_step997 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1010 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_980 p8_1006r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1009
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1008

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1012 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_980 p8_1004r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1011
  intro _
  exact s8_step1010 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1017 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1004 p8_1013r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1016
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1015

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1019 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1004 p8_1004l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1018
  intro _
  exact s8_step1017 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1021 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_980 p8_1002r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1020
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1019 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1012 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1027 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1002 p8_1023r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1026
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1025

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1029 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1002 p8_1022r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1028
  intro _
  exact s8_step1027 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1031 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1002 p8_1002l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1030
  intro _
  exact s8_step1029 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1033 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_980 p8_1000r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1032
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1031 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1021 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1035 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_883 p8_979r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 2 <|
         Hubcap.one 6 2 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 3 4 6 <|
         Hubcap.two 5 7 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_1034
    intro _
    exact s8_step1033 hred L1_1 L1_2 L2_1
  intro L4_1
  exact s8_step999 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1038 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_883 p8_883l := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1037
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1036
  intro _
  exact s8_step1035 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1039 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_120 p8_739r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
    · exact s8_step1038 hred L1_1 L1_2 L2_1
    intro _
    exact s8_step977 hred L1_1 L1_2 L2_1
  intro L2_2
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step882 hred L1_1 L1_2 L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact s8_step814 hred L1_1 L1_2 L2_1 L2_2
  intro _
  exact s8_step795 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1042 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_120 p8_737r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1041
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1040
  intro _
  exact s8_step1039 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1060 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047)
    (L3_3 : Successful q8_1052) :
    SucceedsIn q8_737 p8_1056r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1059
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1058

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1063 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047)
    (L3_3 : Successful q8_1052) :
    SucceedsIn q8_737 p8_1054r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1062
  intro _
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 7 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1061
  intro _
  exact s8_step1060 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1065 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047)
    (L3_3 : Successful q8_1052) :
    SucceedsIn q8_737 p8_1052r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1064
  intro _
  exact s8_step1063 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1081 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1077r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1080
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1079

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1083 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1076r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1082
  intro _
  exact s8_step1081 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1085 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1074r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1084
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1083 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1088 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1072r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1087
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1086
  intro _
  exact s8_step1085 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1090 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1070r := by
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1089
  intro _
  exact s8_step1088 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1097 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1070 p8_1093r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1096
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1095

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1100 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1070 p8_1091r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1099
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1098
  intro _
  exact s8_step1097 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1102 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1069r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 2 2 <|
         Hubcap.one 5 3 <|
         Hubcap.one 6 0 <|
         Hubcap.one 7 3 <|
         Hubcap.two 0 1 6 <|
         Hubcap.two 3 4 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_1101
    intro _
    exact s8_step1100 hred L1_1 L1_2 L2_1 L3_1 L3_2
  intro _
  exact s8_step1090 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1104 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1068r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1103
  intro _
  exact s8_step1102 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1107 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1066r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1106
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1105
  intro _
  exact s8_step1104 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1109 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_1052 p8_1052l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1108
  intro _
  exact s8_step1107 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1111 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045)
    (L3_2 : Successful q8_1047) :
    SucceedsIn q8_737 p8_1050r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1110
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1109 hred L1_1 L1_2 L2_1 L3_1 L3_2
  intro L3_3
  exact s8_step1065 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1122 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1118r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1121
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1120

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1124 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1117r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1123
  intro _
  exact s8_step1122 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1126 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1116r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1125
  intro _
  exact s8_step1124 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1128 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1114r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1127
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1126 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1130 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1113r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1129
  intro _
  exact s8_step1128 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1132 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1112r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1131
  intro _
  exact s8_step1130 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1134 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_1047 p8_1047l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 1 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1133
  intro _
  exact s8_step1132 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1135 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1045) :
    SucceedsIn q8_737 p8_1046r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1134 hred L1_1 L1_2 L2_1 L3_1
  intro L3_2
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1111 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1145 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1045 p8_1141r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1144
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1143

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1149 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1141 p8_1141l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1148
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1147

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1151 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1045 p8_1139r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1150
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1149 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1145 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1157 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1139 p8_1153r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1156
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1155

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1159 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1139 p8_1152r := by
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1158
  intro _
  exact s8_step1157 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1161 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1139 p8_1139l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1160
  intro _
  exact s8_step1159 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1163 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1045 p8_1137r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1162
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1161 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1151 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1166 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1045 p8_1045l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1165
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1164
  intro _
  exact s8_step1163 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_737 p8_1043r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1167
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s8_step1166 hred L1_1 L1_2 L2_1
  intro L3_1
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1135 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1170 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_737 p8_737l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1169
  intro _
  exact s8_step1168 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1172 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_120 p8_735r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 7 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1171
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s8_step1170 hred L1_1 L1_2 L2_1
  intro _
  exact s8_step1042 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1175 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_120 p8_733r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1174
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1173
  intro _
  exact s8_step1172 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1195 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185)
    (L3_3 : Successful q8_1187) :
    SucceedsIn q8_733 p8_1191r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1194
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1198 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185)
    (L3_3 : Successful q8_1187) :
    SucceedsIn q8_733 p8_1189r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1197
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1196
  intro _
  exact s8_step1195 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1200 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185)
    (L3_3 : Successful q8_1187) :
    SucceedsIn q8_733 p8_1187r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1199
  intro _
  exact s8_step1198 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1213 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185) :
    SucceedsIn q8_1187 p8_1209r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1212
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1211

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1215 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185) :
    SucceedsIn q8_1187 p8_1208r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1214
  intro _
  exact s8_step1213 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1217 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185) :
    SucceedsIn q8_1187 p8_1205r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1216
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1215 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1220 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185) :
    SucceedsIn q8_1187 p8_1203r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1219
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1218
  intro _
  exact s8_step1217 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1223 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178)
    (L3_2 : Successful q8_1185) :
    SucceedsIn q8_1187 p8_1201r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1222
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1221
  intro _
  exact s8_step1220 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1241 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1237r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1240
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1239

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1243 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1235r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1242
  intro _
  exact s8_step1241 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1246 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1233r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1245
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 3 1 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1244
  intro _
  exact s8_step1243 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1248 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1230r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1247
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1246 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1250 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1229r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1249
  intro _
  exact s8_step1248 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1253 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1227r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1252
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1251
  intro _
  exact s8_step1250 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1255 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1225r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1254
  intro _
  exact s8_step1253 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1257 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_1185 p8_1185l := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1256
  intro _
  exact s8_step1255 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1258 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_733 p8_1184r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact s8_step1257 hred L1_1 L1_2 L2_1 L3_1
  intro L3_2
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1223 hred L1_1 L1_2 L2_1 L3_1 L3_2
  intro L3_3
  exact s8_step1200 hred L1_1 L1_2 L2_1 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1261 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_733 p8_1182r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1260
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1259
  intro _
  exact s8_step1258 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1264 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L3_1 : Successful q8_1178) :
    SucceedsIn q8_733 p8_1180r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 4 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1263
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1262
  intro _
  exact s8_step1261 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1285 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1281r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1284
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1287 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1279r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1286
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1285 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1289 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1277r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1288
  intro _
  exact s8_step1287 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1291 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1275r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1290
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1289 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1293 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1273r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1292
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step1291 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1296 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1271r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1295
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1294
  intro _
  exact s8_step1293 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1311 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1307r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1310
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1309

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1314 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1305r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1313
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1312
  intro _
  exact s8_step1311 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1316 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1303r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1315
  intro _
  exact s8_step1314 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1319 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1301r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1318
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1317
  intro _
  exact s8_step1316 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1321 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1300r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1320
  intro _
  exact s8_step1319 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1324 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1298r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1323
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1322
  intro _
  exact s8_step1321 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1327 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1271 p8_1271l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1326
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1325
  intro _
  exact s8_step1324 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1269) :
    SucceedsIn q8_1178 p8_1269r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 2 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1328
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1327 hred L1_1 L1_2 L2_1 L4_1
  intro _
  exact s8_step1296 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1338 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1269 p8_1334r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1337
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1336

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1341 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1269 p8_1332r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1340
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1339
  intro _
  exact s8_step1338 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1344 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1269 p8_1330r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1343
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 7 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1342
  intro _
  exact s8_step1341 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1346 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1178 p8_1268r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 6 4 <|
         Hubcap.one 7 3 <|
         Hubcap.two 0 1 4 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 4 5 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_1345
    intro _
    exact s8_step1344 hred L1_1 L1_2 L2_1
  intro L4_1
  exact s8_step1329 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1348 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1178 p8_1267r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1347
  intro _
  exact s8_step1346 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1350 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1178 p8_1266r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1349
  intro _
  exact s8_step1348 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1353 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1178 p8_1178l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1352
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1351
  intro _
  exact s8_step1350 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1373 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360)
    (L4_3 : Successful q8_1364) :
    SucceedsIn q8_1177 p8_1369r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1372
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1371

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1376 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360)
    (L4_3 : Successful q8_1364) :
    SucceedsIn q8_1177 p8_1367r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1375
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 3 <|
       Hubcap.two 2 6 7 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1374
  intro _
  exact s8_step1373 hred L1_1 L1_2 L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1379 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360)
    (L4_3 : Successful q8_1364) :
    SucceedsIn q8_1177 p8_1365r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1378
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 3 <|
       Hubcap.two 1 7 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1377
  intro _
  exact s8_step1376 hred L1_1 L1_2 L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1387 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1364 p8_1383r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 6 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1386
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1385

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1390 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1364 p8_1381r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1389
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1388
  intro _
  exact s8_step1387 hred L1_1 L1_2 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1393 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1364 p8_1364l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1392
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1391
  intro _
  exact s8_step1390 hred L1_1 L1_2 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1398 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1363 p8_1394r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1397
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1396

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1399 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1177 p8_1362r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1398 hred L1_1 L1_2 L2_1 L4_1 L4_2
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1393 hred L1_1 L1_2 L2_1 L4_1 L4_2
  intro L4_3
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step1379 hred L1_1 L1_2 L2_1 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1405 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1362 p8_1401r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1404
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1403

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1407 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L4_2 : Successful q8_1360) :
    SucceedsIn q8_1362 p8_1400r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1406
  intro _
  exact s8_step1405 hred L1_1 L1_2 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1419 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1360 p8_1415r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 2 6 8 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1418
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1417

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1421 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1360 p8_1414r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1420
  intro _
  exact s8_step1419 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1430 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1413 p8_1426r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1429
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1428

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1432 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1413 p8_1425r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1431
  intro _
  exact s8_step1430 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1434 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1413 p8_1424r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1433
  intro _
  exact s8_step1432 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1436 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1413 p8_1423r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1435
  intro _
  exact s8_step1434 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1437 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1360 p8_1412r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L5_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s8_step1436 hred L1_1 L1_2 L2_1 L4_1 L5_1
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 6 8 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1422
  intro _
  exact s8_step1421 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1439 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358)
    (L5_1 : Successful q8_1410) :
    SucceedsIn q8_1360 p8_1411r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1438
  intro _
  exact s8_step1437 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1445 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358) :
    SucceedsIn q8_1410 p8_1441r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1444
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1443

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1446 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358) :
    SucceedsIn q8_1360 p8_1409r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1445 hred L1_1 L1_2 L2_1 L4_1
  intro L5_1
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 2 <|
       Hubcap.two 2 5 7 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1440
  intro _
  exact s8_step1439 hred L1_1 L1_2 L2_1 L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1449 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358) :
    SucceedsIn q8_1360 p8_1360l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1448
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 8 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1447
  intro _
  exact s8_step1446 hred L1_1 L1_2 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1450 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731)
    (L4_1 : Successful q8_1358) :
    SucceedsIn q8_1177 p8_1359r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step1449 hred L1_1 L1_2 L2_1 L4_1
  intro L4_2
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step1407 hred L1_1 L1_2 L2_1 L4_1 L4_2
  intro _
  exact s8_step1399 hred L1_1 L1_2 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1456 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1358 p8_1452r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1455
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1454

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1458 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1358 p8_1451r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1457
  intro _
  exact s8_step1456 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1460 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1358 p8_1358l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1459
  intro _
  exact s8_step1458 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1473 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1357 p8_1469r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1472
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1471

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step1480 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q8_116)
    (L1_2 : Successful q8_118)
    (L2_1 : Successful q8_731) :
    SucceedsIn q8_1468 p8_1476r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_1479
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_1478

end FourColor

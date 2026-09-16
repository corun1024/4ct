import FourColor.Present7Step12
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 13 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6028 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991)
    (L8_1 : Successful q7_6024) :
    SucceedsIn q7_6009 p7_6024r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L8_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6027

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6033 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991) :
    SucceedsIn q7_6024 p7_6029r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6032
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6031

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6035 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991) :
    SucceedsIn q7_6009 p7_6009l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 5 <|
         Hubcap.one 3 (-2) <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 1 <|
         Hubcap.one 6 (-1) <|
         Hubcap.two 0 2 7 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_6034
    intro _
    exact s7_step6033 hred L6_1
  intro L8_1
  exact s7_step6028 hred L6_1 L8_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6036 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q7_5991) :
    SucceedsIn q7_5942 p7_5992r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
    · exact s7_step6035 hred L6_1
    intro L7_1
    refine succeed_by_split .spoke 6 8 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L7_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step6023 hred L6_1 L7_1
  intro L6_2
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L6_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step6008 hred L6_1 L6_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6041 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5991 p7_6037r := by
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_6040
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_6039

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6043 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5942 p7_5942l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 5 <|
         Hubcap.one 3 (-2) <|
         Hubcap.one 4 0 <|
         Hubcap.two 0 2 7 <|
         Hubcap.two 5 6 0 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_6042
    intro _
    exact s7_step6041 hred
  intro L6_1
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step6036 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6044 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5795l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact s7_step6043 hred
    intro _
    exact s7_step5990 hred
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5941 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6045 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_4976 p7_4976l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step6044 hred
  intro L3_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5825 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step6046 (hred : RedpartSound theRedpart) :
    SucceedsIn p7_0 p7_0 := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
      · exact s7_step6045 hred
      intro L2_1
      refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 6 false L2_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s7_step5792 hred L2_1
    intro L1_1
    exact s7_step4975 hred L1_1
  intro L0_1
  exact s7_step876 hred L0_1

end FourColor

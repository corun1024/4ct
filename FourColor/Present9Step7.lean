import FourColor.Present9Step6
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 7 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3041 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3002 p9_3002l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 8 6 <|
       Hubcap.two 3 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3040
  intro _
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3039 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3043 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3000r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3042
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3041 hred L3_1 L4_1
  intro _
  exact s9_step3023 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3045 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_2999r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 4 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3044
  intro _
  exact s9_step3043 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3069 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3065r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3068
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3067

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3071 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3063r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3070
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3069 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3073 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3062r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3072
  intro _
  exact s9_step3071 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3075 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3061r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3074
  intro _
  exact s9_step3073 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3085 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3060 p9_3081r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3084
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3083

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3087 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3060 p9_3078r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3086
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3085 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3089 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3060 p9_3077r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3088
  intro _
  exact s9_step3087 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3091 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3060 p9_3060l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3090
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3089 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3093 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3057r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 5 8 <|
       Hubcap.two 2 6 7 <|
       Hubcap.two 2 8 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3092
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3091 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3075 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3096 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3055r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3095
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 8 7 <|
       Hubcap.two 3 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3094
  intro _
  exact s9_step3093 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3104 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3053r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact h9_3103 hred _
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 3 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3097
  intro _
  exact s9_step3096 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3106 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2996 p9_3052r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3105
  intro _
  exact s9_step3104 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3113 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_2995r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact h9_3112 hred _
    intro _
    exact s9_step3106 hred L3_1 L4_1
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact h9_3051 hred _
  intro _
  exact s9_step3045 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3115 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_2994r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3114
  intro _
  exact s9_step3113 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3117 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_2993r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3116
  intro _
  exact s9_step3115 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3132 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2724r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact h9_3131 hred _
    intro _
    exact s9_step3117 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact s9_step2991 hred L3_1 L4_1
    intro L5_1
    refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 true L5_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step2901 hred L3_1 L4_1 L5_1
  intro _
  exact s9_step2895 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3149 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3145r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3148
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3147

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3151 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3143r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3150
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3149 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3154 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3141r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3153
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3152
  intro _
  exact s9_step3151 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3161 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3140 p9_3157r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3160
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3159

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3162 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3139r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3161 hred L3_1
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3155
  intro _
  exact s9_step3154 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3165 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3137r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3164
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3163
  intro _
  exact s9_step3162 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3167 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3136r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3166
  intro _
  exact s9_step3165 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3169 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_3135r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3168
  intro _
  exact s9_step3167 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3191 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3187r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3190
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3189

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3193 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3186r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3192
  intro _
  exact s9_step3191 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3195 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3185r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3194
  intro _
  exact s9_step3193 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3197 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3184r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3196
  intro _
  exact s9_step3195 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3199 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3182r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3198
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3197 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3201 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3180r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3200
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3199 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3203 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3179r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 2 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3202
  intro _
  exact s9_step3201 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3205 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3177r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 8 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3204
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3203 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3215 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3177 p9_3211r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3214
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 7 9 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3213

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3217 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3177 p9_3210r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3216
  intro _
  exact s9_step3215 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3219 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3177 p9_3209r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3218
  intro _
  exact s9_step3217 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3221 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3177 p9_3207r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3220
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3219 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3223 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3177 p9_3177l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3222
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3221 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3231 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3174r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3230
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact h9_3229 hred _
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s9_step3223 hred L3_1
  intro _
  exact s9_step3205 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3233 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3173r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3232
  intro _
  exact s9_step3231 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3241 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3171r := by
  refine succeed_by_split .spoke 2 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3240
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact h9_3239 hred _
  intro _
  exact s9_step3233 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3252 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3248r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3251
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3250

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3254 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3247r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3253
  intro _
  exact s9_step3252 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3256 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3246r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3255
  intro _
  exact s9_step3254 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3258 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3245r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3257
  intro _
  exact s9_step3256 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3260 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3244r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3259
  intro _
  exact s9_step3258 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3262 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3171 p9_3243r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3261
  intro _
  exact s9_step3260 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3289 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3135 p9_3135l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact h9_3288 hred _
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3262 hred L3_1
  intro _
  exact s9_step3241 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3305 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3293 p9_3301r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3304
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3303

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3307 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3293 p9_3298r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3306
  intro _
  refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3305 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3309 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3293 p9_3297r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3308
  intro _
  exact s9_step3307 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3311 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3293 p9_3296r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 4 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3310
  intro _
  exact s9_step3309 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3313 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3293 p9_3293l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3312
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3311 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3315 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3134 p9_3291r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3314
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3313 hred L3_1
  intro L6_1
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3317 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_3134 p9_3290r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3316
  intro _
  exact s9_step3315 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3318 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_2724 p9_2724l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s9_step3317 hred L3_1
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact s9_step3289 hred L3_1
  intro _
  exact s9_step3169 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3319 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541) :
    SucceedsIn q9_792 p9_2542r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact s9_step3318 hred L3_1
    intro L4_1
    exact s9_step3132 hred L3_1 L4_1
  intro L3_2
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact s9_step2723 hred L3_1 L3_2
  intro L3_3
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2614 hred L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3337 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322)
    (L4_3 : Successful q9_3331) :
    SucceedsIn q9_2541 p9_3333r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3336
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3335

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3339 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322)
    (L4_3 : Successful q9_3331) :
    SucceedsIn q9_2541 p9_3332r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3338
  intro _
  exact s9_step3337 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3345 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3331 p9_3341r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3344
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3343

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3348 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3331 p9_3331l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3347
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3346
  intro _
  exact s9_step3345 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3355 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3330 p9_3351r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3354
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3353

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3357 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3330 p9_3349r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3356
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3355 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3359 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3330 p9_3330l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3358
  intro _
  exact s9_step3357 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3361 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_2541 p9_3328r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3360
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3359 hred L4_1 L4_2
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3348 hred L4_1 L4_2
  intro L4_3
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3339 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3363 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_2541 p9_3327r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3362
  intro _
  exact s9_step3361 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3365 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_2541 p9_3326r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3364
  intro _
  exact s9_step3363 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3367 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_2541 p9_3325r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3366
  intro _
  exact s9_step3365 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3369 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_2541 p9_3324r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3368
  intro _
  exact s9_step3367 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3385 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322)
    (L5_1 : Successful q9_3377) :
    SucceedsIn q9_3324 p9_3382r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3384

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3386 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322)
    (L5_1 : Successful q9_3377) :
    SucceedsIn q9_3324 p9_3378r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3385 hred L4_1 L4_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3391 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3377 p9_3387r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3390
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3389

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3393 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3377 p9_3377l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3392
  intro _
  exact s9_step3391 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3395 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3375r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3394
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3393 hred L4_1 L4_2
  intro L5_1
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3386 hred L4_1 L4_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3397 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3374r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3396
  intro _
  exact s9_step3395 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3399 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3373r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3398
  intro _
  exact s9_step3397 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3401 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3372r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3400
  intro _
  exact s9_step3399 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3403 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3371r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3402
  intro _
  exact s9_step3401 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3405 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3370r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3404
  intro _
  exact s9_step3403 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3407 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320)
    (L4_2 : Successful q9_3322) :
    SucceedsIn q9_3324 p9_3324l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3406
  intro _
  exact s9_step3405 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3429 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3425r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3428
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3427

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3431 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3424r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3430
  intro _
  exact s9_step3429 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3433 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3423r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3432
  intro _
  exact s9_step3431 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3435 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3420r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 8 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3434
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3433 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3437 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3417r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3436
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3435 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3449 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3445r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3448
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3447

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3451 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3443r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3450
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3449 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3453 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3442r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3452
  intro _
  exact s9_step3451 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3455 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3441r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3454
  intro _
  exact s9_step3453 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3457 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3438r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3456
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3455 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3459 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3416 p9_3416l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3458
  intro _
  exact s9_step3457 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3461 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3414r := by
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3460
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3459 hred L4_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3437 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3470 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3414 p9_3466r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3469
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3468

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3472 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3414 p9_3463r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3471
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3470 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3474 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3414 p9_3462r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3473
  intro _
  exact s9_step3472 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3476 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3414 p9_3414l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3475
  intro _
  exact s9_step3474 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3478 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3412r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3477
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3476 hred L4_1
  intro _
  exact s9_step3461 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3480 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3411r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3479
  intro _
  exact s9_step3478 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3482 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3410r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3481
  intro _
  exact s9_step3480 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3495 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3491r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3494
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3493

end FourColor

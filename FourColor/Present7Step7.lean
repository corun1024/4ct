import FourColor.Present7Step6
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 7 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3230 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199) :
    SucceedsIn q7_3175 p7_3200r := by
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3229 hred L1_1 L1_2 L2_1 L3_1
  intro L3_2
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3224 hred L1_1 L1_2 L2_1 L3_1 L3_2
  intro _
  exact s7_step3211 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3241 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3199 p7_3237r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3240
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3239

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3243 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3199 p7_3236r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3242
  intro _
  exact s7_step3241 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3245 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3199 p7_3233r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3244
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3243 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3253 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3233 p7_3249r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3252
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3251

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3255 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3233 p7_3248r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3254
  intro _
  exact s7_step3253 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3257 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3233 p7_3233l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3256
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3255 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3259 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3199 p7_3199l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3258
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3257 hred L1_1 L1_2 L2_1
  intro _
  exact s7_step3245 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3260 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_3175 p7_3175l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s7_step3259 hred L1_1 L1_2 L2_1
  intro L3_1
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3231
  intro _
  exact s7_step3230 hred L1_1 L1_2 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3261 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172) :
    SucceedsIn q7_881 p7_3172r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s7_step3260 hred L1_1 L1_2 L2_1
  intro L2_2
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3198 hred L1_1 L1_2 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3275 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3172 p7_3271r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 0 1 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3274
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3273

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3278 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3172 p7_3269r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 3 <|
       Hubcap.two 0 1 1 <|
       Hubcap.two 2 5 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3277
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-2) <|
       Hubcap.one 3 3 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3276
  intro _
  exact s7_step3275 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3291 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3268 p7_3287r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3290
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3289

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3293 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3268 p7_3286r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3292
  intro _
  exact s7_step3291 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3295 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3268 p7_3284r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3294
  intro _
  exact s7_step3293 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3298 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3268 p7_3282r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3297
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3296
  intro _
  exact s7_step3295 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3301 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3268 p7_3280r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3300
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3299
  intro _
  exact s7_step3298 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3303 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3172 p7_3267r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 6 2 <|
         Hubcap.two 0 1 2 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3302
    intro _
    exact s7_step3301 hred L1_1 L1_2
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3279
  intro _
  exact s7_step3278 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3305 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3172 p7_3265r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3304
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3303 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3315 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3264 p7_3311r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.two 2 6 1 <|
       Hubcap.two 4 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3314
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3313

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3318 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3264 p7_3309r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3317
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3316
  intro _
  exact s7_step3315 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3320 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3264 p7_3307r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 2 6 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3319
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3318 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3329 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3307 p7_3325r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3328
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3327

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3332 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3307 p7_3323r := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3331
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3330
  intro _
  exact s7_step3329 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3338 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3323 p7_3334r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3337
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3336

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3341 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3323 p7_3323l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3340
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3339
  intro _
  exact s7_step3338 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3343 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3307 p7_3307l := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3342
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step3341 hred L1_1 L1_2
  intro _
  exact s7_step3332 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3344 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3172 p7_3263r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s7_step3343 hred L1_1 L1_2
    intro _
    exact s7_step3320 hred L1_1 L1_2
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3306
  intro _
  exact s7_step3305 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3351 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3263 p7_3347r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 0 1 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3350
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3349

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3354 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3263 p7_3345r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3353
  intro _
  refine succeed_by_split .spoke 4 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.two 0 1 2 <|
       Hubcap.two 2 4 1 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 3 6 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3352
  intro _
  exact s7_step3351 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3359 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3345 p7_3355r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 1 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3358
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3357

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3368 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3355 p7_3364r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3367
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3366

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3371 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3355 p7_3362r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3370
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3369
  intro _
  exact s7_step3368 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3374 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3355 p7_3360r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3373
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3372
  intro _
  exact s7_step3371 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3376 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3345 p7_3345l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 3 2 <|
         Hubcap.two 0 4 2 <|
         Hubcap.two 1 5 3 <|
         Hubcap.two 1 6 5 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3375
    intro _
    exact s7_step3374 hred L1_1 L1_2
  intro _
  exact s7_step3359 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3389 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378)
    (L4_2 : Successful q7_3380)
    (L4_3 : Successful q7_3382) :
    SucceedsIn q7_3262 p7_3386r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3388

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3390 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378)
    (L4_2 : Successful q7_3380)
    (L4_3 : Successful q7_3382) :
    SucceedsIn q7_3262 p7_3382r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3389 hred L1_1 L1_2 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3396 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378)
    (L4_2 : Successful q7_3380) :
    SucceedsIn q7_3382 p7_3392r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3395

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3397 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378)
    (L4_2 : Successful q7_3380) :
    SucceedsIn q7_3262 p7_3380r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3396 hred L1_1 L1_2 L4_1 L4_2
  intro L4_3
  exact s7_step3390 hred L1_1 L1_2 L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3403 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378) :
    SucceedsIn q7_3380 p7_3399r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3402
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3401

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3408 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378) :
    SucceedsIn q7_3399 p7_3404r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3407

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3410 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L4_1 : Successful q7_3378) :
    SucceedsIn q7_3380 p7_3380l := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3409
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3408 hred L1_1 L1_2 L4_1
  intro _
  exact s7_step3403 hred L1_1 L1_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3416 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3378 p7_3412r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3415
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3414

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3419 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3378 p7_3378l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3418
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3417
  intro _
  exact s7_step3416 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3428 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3420 p7_3424r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3427
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3426

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3431 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3420 p7_3422r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3430
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3429
  intro _
  exact s7_step3428 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3433 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3377 p7_3377l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 3 2 <|
         Hubcap.one 5 0 <|
         Hubcap.two 1 2 2 <|
         Hubcap.two 4 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3432
    intro _
    exact s7_step3431 hred L1_1 L1_2
  intro L5_1
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3434 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_3262 p7_3262l := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s7_step3433 hred L1_1 L1_2
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s7_step3419 hred L1_1 L1_2
  intro L4_1
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step3410 hred L1_1 L1_2 L4_1
  intro L4_2
  exact s7_step3397 hred L1_1 L1_2 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3435 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_881 p7_3171r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step3434 hred L1_1 L1_2
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
      · exact s7_step3376 hred L1_1 L1_2
      intro _
      exact s7_step3354 hred L1_1 L1_2
    intro _
    exact s7_step3344 hred L1_1 L1_2
  intro L2_1
  exact s7_step3261 hred L1_1 L1_2 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3436 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879) :
    SucceedsIn q7_1 p7_880r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step3435 hred L1_1 L1_2
  intro L1_3
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 false L1_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact s7_step3170 hred L1_1 L1_2 L1_3
  intro L1_4
  exact s7_step1818 hred L1_1 L1_2 L1_3 L1_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3452 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L2_3 : Successful q7_3444) :
    SucceedsIn q7_879 p7_3448r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3451
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3450

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3455 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L2_3 : Successful q7_3444) :
    SucceedsIn q7_879 p7_3446r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3454
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3453
  intro _
  exact s7_step3452 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3457 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L2_3 : Successful q7_3444) :
    SucceedsIn q7_879 p7_3444r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3456
  intro _
  exact s7_step3455 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3470 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459)
    (L3_3 : Successful q7_3465) :
    SucceedsIn q7_3444 p7_3466r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3469
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3468

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3483 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3465 p7_3479r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3482
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3481

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3485 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3465 p7_3477r := by
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3484
  intro _
  exact s7_step3483 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3488 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3465 p7_3475r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3487
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3486
  intro _
  exact s7_step3485 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3491 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3465 p7_3473r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3490
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3489
  intro _
  exact s7_step3488 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3494 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3465 p7_3471r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3493
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3492
  intro _
  exact s7_step3491 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3496 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3444 p7_3464r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 1 <|
         Hubcap.one 2 2 <|
         Hubcap.two 3 4 2 <|
         Hubcap.two 5 6 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3495
    intro _
    exact s7_step3494 hred L1_1 L2_1 L2_2 L3_1 L3_2
  intro L3_3
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3470 hred L1_1 L2_1 L2_2 L3_1 L3_2 L3_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3502 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3464 p7_3498r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3501
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3500

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3505 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3464 p7_3464l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3504
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 1 5 2 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3503
  intro _
  exact s7_step3502 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3507 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3444 p7_3462r := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3506
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact s7_step3505 hred L1_1 L2_1 L2_2 L3_1 L3_2
  intro _
  exact s7_step3496 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3516 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3460 p7_3512r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3515
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3514

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3519 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3460 p7_3510r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3518
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3517
  intro _
  exact s7_step3516 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3521 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3460 p7_3508r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3520
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3519 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3523 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458)
    (L3_2 : Successful q7_3459) :
    SucceedsIn q7_3444 p7_3459r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 0 1 3 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3522
    intro _
    exact s7_step3521 hred L1_1 L2_1 L2_2 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3507 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3530 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458) :
    SucceedsIn q7_3459 p7_3526r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3529
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3528

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3533 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458) :
    SucceedsIn q7_3459 p7_3524r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3532
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3531
  intro _
  exact s7_step3530 hred L1_1 L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3535 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441)
    (L3_1 : Successful q7_3458) :
    SucceedsIn q7_3444 p7_3458r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 2 <|
         Hubcap.one 6 0 <|
         Hubcap.two 1 3 4 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3534
    intro _
    exact s7_step3533 hred L1_1 L2_1 L2_2 L3_1
  intro L3_2
  exact s7_step3523 hred L1_1 L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3543 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3458 p7_3539r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3542
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3541

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3546 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3458 p7_3537r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3545
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3544
  intro _
  exact s7_step3543 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3555 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3537 p7_3551r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3554
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3553

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3558 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3537 p7_3549r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3557
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3556
  intro _
  exact s7_step3555 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3563 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3547 p7_3559r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3562
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3561

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3565 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3547 p7_3547l := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3564
  intro _
  exact s7_step3563 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3566 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3458 p7_3536r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
    · exact s7_step3565 hred L1_1 L2_1 L2_2
    intro _
    refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3558 hred L1_1 L2_1 L2_2
  intro _
  exact s7_step3546 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3574 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3443 p7_3570r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3573
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3572

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3576 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3443 p7_3568r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3575
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3574 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3578 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_3443 p7_3567r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3577
  intro _
  exact s7_step3576 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3580 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L2_2 : Successful q7_3441) :
    SucceedsIn q7_879 p7_3442r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 2 <|
         Hubcap.two 3 6 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3579
    intro _
    exact s7_step3578 hred L1_1 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
      · exact succeed_by_reducibility hred (by decide +kernel)
      intro _
      exact s7_step3566 hred L1_1 L2_1 L2_2
    intro L3_1
    exact s7_step3535 hred L1_1 L2_1 L2_2 L3_1
  intro L2_3
  exact s7_step3457 hred L1_1 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3591 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3441 p7_3587r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3590
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3589

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3601 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3586 p7_3597r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3600
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3599

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3604 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3586 p7_3595r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3603
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3602
  intro _
  exact s7_step3601 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3606 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3586 p7_3594r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3605
  intro _
  exact s7_step3604 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3609 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3586 p7_3586l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3608
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3607
  intro _
  exact s7_step3606 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3610 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3441 p7_3585r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3609 hred L1_1 L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3592
  intro _
  exact s7_step3591 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3619 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3585 p7_3615r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3618
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3617

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3622 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3585 p7_3613r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3621
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3620
  intro _
  exact s7_step3619 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3624 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3585 p7_3611r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3623
  intro _
  exact s7_step3622 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3630 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3584 p7_3627r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3629

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3644 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3640r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3643
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3642

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3646 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3639r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3645
  intro _
  exact s7_step3644 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3649 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3637r := by
  refine succeed_by_split .spoke 1 8 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3648
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3647
  intro _
  exact s7_step3646 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3651 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3635r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.two 0 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3650
  intro _
  refine succeed_by_split .fan2 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3649 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3653 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3633r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 4 5 1 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3652
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3651 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3655 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3627 p7_3631r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3654
  intro _
  exact s7_step3653 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3657 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3584 p7_3626r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 2 2 <|
         Hubcap.one 4 (-2) <|
         Hubcap.two 1 3 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3656
    intro _
    exact s7_step3655 hred L1_1 L2_1 L3_1 L3_2
  intro _
  exact s7_step3630 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3676 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3672r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3675
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3674

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3678 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3670r := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3677
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3676 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3681 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3668r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3680
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3679
  intro _
  exact s7_step3678 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3683 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3666r := by
  refine succeed_by_split .fan1 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3682
  intro _
  refine succeed_by_split .fan2 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3681 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3686 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3664r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3685
  intro _
  refine succeed_by_split .fan1 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3684
  intro _
  exact s7_step3683 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3689 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3662r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3688
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3687
  intro _
  exact s7_step3686 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3692 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3660r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 4 2 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3691
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3690
  intro _
  exact s7_step3689 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3694 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3625 p7_3625l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3693
  intro _
  exact s7_step3692 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3695 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3584 p7_3584l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3694 hred L1_1 L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3658
  intro _
  exact s7_step3657 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3702 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581)
    (L3_2 : Successful q7_3582) :
    SucceedsIn q7_3441 p7_3582r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact h7_3701 hred _
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s7_step3695 hred L1_1 L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step3624 hred L1_1 L2_1 L3_1 L3_2
  intro _
  exact s7_step3610 hred L1_1 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3711 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3582 p7_3707r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3710
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3709

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3718 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3706 p7_3714r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3717
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3716

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3720 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3706 p7_3713r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3719
  intro _
  exact s7_step3718 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3722 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3706 p7_3706l := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 4 1 <|
       Hubcap.two 1 6 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3721
  intro _
  exact s7_step3720 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3723 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3582 p7_3705r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3722 hred L1_1 L2_1 L3_1
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3712
  intro _
  exact s7_step3711 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3738 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3734r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3737
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3736

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3741 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3732r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3740
  intro _
  refine succeed_by_split .spoke 1 8 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3739
  intro _
  exact s7_step3738 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3744 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3730r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3743
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3742
  intro _
  exact s7_step3741 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3746 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3729r := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3745
  intro _
  exact s7_step3744 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3748 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3727r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-2) <|
       Hubcap.one 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3747
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3746 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3751 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3725r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3750
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3749
  intro _
  exact s7_step3748 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3753 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3705 p7_3705l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3752
  intro _
  exact s7_step3751 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3755 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L3_1 : Successful q7_3581) :
    SucceedsIn q7_3582 p7_3703r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3754
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3753 hred L1_1 L2_1 L3_1
  intro _
  exact s7_step3723 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3771 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3767r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3770
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3769

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3773 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3765r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3772
  intro _
  refine succeed_by_split .fan2 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3771 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3776 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3763r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 1 5 4 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3775
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 0 <|
       Hubcap.two 1 5 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3774
  intro _
  exact s7_step3773 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3778 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3762r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 5 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3777
  intro _
  exact s7_step3776 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3781 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3760r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3780
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3779
  intro _
  exact s7_step3778 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3784 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3581 p7_3758r := by
  refine succeed_by_split .spoke 1 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3783
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3782
  intro _
  exact s7_step3781 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3796 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3758 p7_3792r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3795
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3794

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3798 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3758 p7_3790r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3797
  intro _
  refine succeed_by_split .fan2 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3796 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3801 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3758 p7_3788r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3800
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3799
  intro _
  exact s7_step3798 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3803 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3758 p7_3785r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 (-1) <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3802
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3801 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3829 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3825r := by
  refine succeed_by_split .fan2 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3828
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3827

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3831 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3824r := by
  refine succeed_by_split .fan2 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3830
  intro _
  exact s7_step3829 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3833 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3822r := by
  refine succeed_by_split .fan1 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3832
  intro _
  refine succeed_by_split .fan2 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3831 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3836 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3757 p7_3820r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3835
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3834
  intro _
  exact s7_step3833 hred L1_1 L2_1

end FourColor

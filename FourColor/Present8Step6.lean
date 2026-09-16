import FourColor.Present8Step5
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 6 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3192 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3173r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 6 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 2 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3191
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3190 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3201 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3172 p8_3197r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.two 2 5 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3200
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3199

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3203 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3172 p8_3195r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3202
  intro _
  exact s8_step3201 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3205 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3172 p8_3172l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3204
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3203 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3206 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3171r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s8_step3205 hred L2_1 L2_2 L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 2 6 6 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3193
  intro _
  exact s8_step3192 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3208 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3169r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.two 2 5 5 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3207
  intro _
  exact s8_step3206 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3220 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3216r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3219
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3218

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3222 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3215r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3221
  intro _
  exact s8_step3220 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3224 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3213r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3223
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3222 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3227 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3211r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3226
  intro _
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3225
  intro _
  exact s8_step3224 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3229 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3210r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3228
  intro _
  exact s8_step3227 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3231 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3209r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3230
  intro _
  exact s8_step3229 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3233 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3169 p8_3169l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 5 6 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3232
  intro _
  exact s8_step3231 hred L2_1 L2_2 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3235 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_3141 p8_3141l := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3234
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3233 hred L2_1 L2_2 L3_1
  intro L4_1
  exact s8_step3208 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3236 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137) :
    SucceedsIn q8_2739 p8_3137r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step3235 hred L2_1 L2_2 L3_1
  intro L3_2
  exact s8_step3167 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3256 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3252r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3255
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3254

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3258 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3251r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3257
  intro _
  exact s8_step3256 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3260 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3250r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3259
  intro _
  exact s8_step3258 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3262 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3249r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3261
  intro _
  exact s8_step3260 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3265 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3247r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3264
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3263
  intro _
  exact s8_step3262 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3267 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3245r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3266
  intro _
  exact s8_step3265 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3275 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3245 p8_3271r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3274
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3273

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3277 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3245 p8_3270r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3276
  intro _
  exact s8_step3275 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3279 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3245 p8_3269r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3278
  intro _
  exact s8_step3277 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3281 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3245 p8_3268r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3280
  intro _
  exact s8_step3279 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3283 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3244r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 5 <|
         Hubcap.one 2 0 <|
         Hubcap.one 5 1 <|
         Hubcap.one 6 3 <|
         Hubcap.two 1 3 5 <|
         Hubcap.two 4 7 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_3282
    intro _
    exact s8_step3281 hred L2_1 L2_2
  intro _
  exact s8_step3267 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3285 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3243r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3284
  intro _
  exact s8_step3283 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3302 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3298r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3301
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3300

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3304 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3296r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3303
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3302 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3306 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3295r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3305
  intro _
  exact s8_step3304 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3308 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3293r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3307
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3306 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3310 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3292r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3309
  intro _
  exact s8_step3308 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3312 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3290r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3311
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3310 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3315 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3242 p8_3288r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3314
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 5 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3313
  intro _
  exact s8_step3312 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3316 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3241r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3315 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 4 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3286
  intro _
  exact s8_step3285 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3318 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3240r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3317
  intro _
  exact s8_step3316 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3327 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3239 p8_3323r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3326
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 5 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3325

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3336 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3321 p8_3332r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3335
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3334

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3338 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3321 p8_3331r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3337
  intro _
  exact s8_step3336 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3341 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3321 p8_3329r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3340
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3339
  intro _
  exact s8_step3338 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3343 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3321 p8_3328r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3342
  intro _
  exact s8_step3341 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3345 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3321 p8_3321l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3344
  intro _
  exact s8_step3343 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3352 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3239 p8_3319r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact h8_3351 hred _
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s8_step3345 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3327 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3354 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3239 p8_3239l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3353
  intro _
  exact s8_step3352 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3366 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3238 p8_3362r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 2 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3365
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3364

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3368 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3238 p8_3360r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3367
  intro _
  exact s8_step3366 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3370 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3238 p8_3359r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3369
  intro _
  exact s8_step3368 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3373 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3238 p8_3357r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3372
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3371
  intro _
  exact s8_step3370 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3375 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3238 p8_3356r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3374
  intro _
  exact s8_step3373 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3376 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3137 p8_3237r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3375 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3354 hred L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3318 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3395 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L5_1 : Successful q8_3387) :
    SucceedsIn q8_3237 p8_3391r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3394
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3393

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3397 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L5_1 : Successful q8_3387) :
    SucceedsIn q8_3237 p8_3390r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3396
  intro _
  exact s8_step3395 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3402 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3387 p8_3398r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3401
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3400

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3404 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3387 p8_3387l := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3403
  intro _
  exact s8_step3402 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3405 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3386r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s8_step3404 hred L2_1 L2_2
  intro L5_1
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3397 hred L2_1 L2_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3407 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3385r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3406
  intro _
  exact s8_step3405 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3409 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3384r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3408
  intro _
  exact s8_step3407 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3412 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3382r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3411
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3410
  intro _
  exact s8_step3409 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3422 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3382 p8_3418r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3421
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3420

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3424 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3382 p8_3417r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3423
  intro _
  exact s8_step3422 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3427 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3382 p8_3415r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3426
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3425
  intro _
  exact s8_step3424 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3429 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3382 p8_3414r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3428
  intro _
  exact s8_step3427 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3431 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3380r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 2 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3430
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3429 hred L2_1 L2_2
  intro _
  exact s8_step3412 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3433 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3379r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3432
  intro _
  exact s8_step3431 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3453 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3449r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3452
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3451

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3455 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3447r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3454
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3453 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3457 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3445r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3456
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3455 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3459 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3444r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3458
  intro _
  exact s8_step3457 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3461 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3443r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3460
  intro _
  exact s8_step3459 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3464 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3441r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 7 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3463
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3462
  intro _
  exact s8_step3461 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3466 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3439 p8_3439l := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3465
  intro _
  exact s8_step3464 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3468 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3377 p8_3437r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3467
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3466 hred L2_1 L2_2
  intro L6_1
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3480 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3436 p8_3476r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3479
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3478

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3483 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3436 p8_3474r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3482
  intro _
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3481
  intro _
  exact s8_step3480 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3485 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3436 p8_3473r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3484
  intro _
  exact s8_step3483 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3487 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3436 p8_3472r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3486
  intro _
  exact s8_step3485 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3489 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3436 p8_3471r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3488
  intro _
  exact s8_step3487 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3490 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3377 p8_3435r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3489 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3469
  intro _
  exact s8_step3468 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3503 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3237 p8_3237l := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact h8_3502 hred _
    intro _
    refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact h8_3496 hred _
    intro _
    exact s8_step3490 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3433 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3531 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3527r := by
  refine succeed_by_split .fan1 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3530
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3529

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3533 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3526r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3532
  intro _
  exact s8_step3531 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3535 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3525r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3534
  intro _
  exact s8_step3533 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3537 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3524r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3536
  intro _
  exact s8_step3535 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3540 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3522r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3539
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3538
  intro _
  exact s8_step3537 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3542 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3520r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3541
  intro _
  exact s8_step3540 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3545 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3518r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3544
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3543
  intro _
  exact s8_step3542 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3547 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3516r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3546
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3545 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3549 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3514r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3548
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3547 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3551 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3513r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3550
  intro _
  exact s8_step3549 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3564 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3512 p8_3560r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3563
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3562

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3566 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3512 p8_3559r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3565
  intro _
  exact s8_step3564 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3568 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3512 p8_3557r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3567
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3566 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3570 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3512 p8_3555r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3569
  intro _
  exact s8_step3568 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3578 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3554 p8_3574r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3577
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3576

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3580 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3554 p8_3572r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3579
  intro _
  exact s8_step3578 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3582 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3554 p8_3571r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3581
  intro _
  exact s8_step3580 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3584 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3554 p8_3554l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3583
  intro _
  exact s8_step3582 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3586 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3512 p8_3512l := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3585
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s8_step3584 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3570 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3587 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3511r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3586 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3552
  intro _
  exact s8_step3551 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3590 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3509r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3589
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 4 6 6 <|
       Hubcap.two 5 7 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3588
  intro _
  exact s8_step3587 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3604 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3600r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3603
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3602

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3606 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3598r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3605
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3604 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3608 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3596r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3607
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3606 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3612 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3595 p8_3595l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3611
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3610

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3614 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3593r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3613
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s8_step3612 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3608 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3617 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3591r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3616
  intro _
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3615
  intro _
  exact s8_step3614 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3619 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3509 p8_3509l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3618
  intro _
  exact s8_step3617 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3621 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3507r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3620
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3619 hred L2_1 L2_2
  intro _
  exact s8_step3590 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3623 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3136 p8_3506r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3622
  intro _
  exact s8_step3621 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3649 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737) :
    SucceedsIn q8_3506 p8_3645r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3648
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3647

end FourColor

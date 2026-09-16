import FourColor.Present8Step9
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 10 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5276 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5257r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5275
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step5274 hred L3_1
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5267 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5278 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5256r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5277
  intro _
  exact s8_step5276 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5284 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5256 p8_5280r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5283
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5286 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5256 p8_5279r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5285
  intro _
  exact s8_step5284 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5288 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5255r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 1 1 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 5 <|
         Hubcap.two 0 5 6 <|
         Hubcap.two 2 7 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_5287
    intro _
    exact s8_step5286 hred L3_1
  intro _
  exact s8_step5278 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5290 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5254r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5289
  intro _
  exact s8_step5288 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5295 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5253 p8_5292r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5294

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5296 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5039 p8_5252r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5295 hred L3_1
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5291
  intro _
  exact s8_step5290 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5305 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5252 p8_5301r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5304
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5303

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5307 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5252 p8_5300r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5306
  intro _
  exact s8_step5305 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5313 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5299 p8_5309r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 (-1) <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5312
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5311

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5314 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5252 p8_5298r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5313 hred L3_1
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 (-1) <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 2 5 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5308
  intro _
  exact s8_step5307 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5316 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_5252 p8_5252l := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5315
  intro _
  exact s8_step5314 hred L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5317 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q8_5037) :
    SucceedsIn q8_2735 p8_5038r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
    · exact s8_step5316 hred L3_1
    intro _
    exact s8_step5296 hred L3_1
  intro L3_2
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5250 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5335 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324)
    (L4_3 : Successful q8_5329) :
    SucceedsIn q8_5037 p8_5331r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 (-1) <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5334
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 (-2) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5333

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5337 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324)
    (L4_3 : Successful q8_5329) :
    SucceedsIn q8_5037 p8_5330r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 (-1) <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5336
  intro _
  exact s8_step5335 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5342 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5329 p8_5338r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5341
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5340

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5344 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5329 p8_5329l := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5343
  intro _
  exact s8_step5342 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5353 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5328 p8_5349r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5352
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5351

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5355 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5328 p8_5346r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5354
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5353 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5357 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5328 p8_5345r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5356
  intro _
  exact s8_step5355 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5359 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5328 p8_5328l := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5358
  intro _
  exact s8_step5357 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5361 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5037 p8_5326r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5360
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact s8_step5359 hred L4_1 L4_2
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s8_step5344 hred L4_1 L4_2
  intro L4_3
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5337 hred L4_1 L4_2 L4_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5363 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L4_2 : Successful q8_5324) :
    SucceedsIn q8_5037 p8_5325r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5362
  intro _
  exact s8_step5361 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5382 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371)
    (L5_3 : Successful q8_5375)
    (L5_4 : Successful q8_5377) :
    SucceedsIn q8_5324 p8_5379r := by
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5381

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5386 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371)
    (L5_3 : Successful q8_5375) :
    SucceedsIn q8_5377 p8_5377l := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5385
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5384

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5387 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371)
    (L5_3 : Successful q8_5375) :
    SucceedsIn q8_5324 p8_5375r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s8_step5386 hred L4_1 L5_1 L5_2 L5_3
  intro L5_4
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5382 hred L4_1 L5_1 L5_2 L5_3 L5_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5392 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371) :
    SucceedsIn q8_5375 p8_5388r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5391
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5390

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5394 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371) :
    SucceedsIn q8_5375 p8_5375l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5393
  intro _
  exact s8_step5392 hred L4_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5396 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371) :
    SucceedsIn q8_5324 p8_5373r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5395
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact s8_step5394 hred L4_1 L5_1 L5_2
  intro L5_3
  exact s8_step5387 hred L4_1 L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5398 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365)
    (L5_2 : Successful q8_5371) :
    SucceedsIn q8_5324 p8_5372r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5397
  intro _
  exact s8_step5396 hred L4_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5406 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5371 p8_5402r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5405
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5404

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5408 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5371 p8_5401r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5407
  intro _
  exact s8_step5406 hred L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5410 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5371 p8_5400r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5409
  intro _
  exact s8_step5408 hred L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5411 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5324 p8_5370r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5410 hred L4_1 L5_1
  intro L5_2
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5398 hred L4_1 L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5413 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5324 p8_5368r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5412
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5411 hred L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5418 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5368 p8_5414r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5417
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5416

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5420 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320)
    (L5_1 : Successful q8_5365) :
    SucceedsIn q8_5324 p8_5366r := by
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5419
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L5_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s8_step5418 hred L4_1 L5_1
  intro _
  exact s8_step5413 hred L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5431 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5365 p8_5427r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5430
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5429

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5433 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5365 p8_5424r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 7 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5432
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5431 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5436 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5365 p8_5422r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5435
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5434
  intro _
  exact s8_step5433 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5437 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5324 p8_5364r := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5436 hred L4_1
  intro L5_1
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5421
  intro _
  exact s8_step5420 hred L4_1 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5439 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5037 p8_5322r := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5438
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5437 hred L4_1
  intro L4_2
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step5363 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5448 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5322 p8_5445r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5447

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5450 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5322 p8_5443r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5449
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5448 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5452 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5322 p8_5442r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5451
  intro _
  exact s8_step5450 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5454 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5322 p8_5441r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5453
  intro _
  exact s8_step5452 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5455 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q8_5320) :
    SucceedsIn q8_5037 p8_5320r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5454 hred L4_1
  intro _
  exact s8_step5439 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5467 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5320 p8_5463r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5466
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5465

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5469 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5320 p8_5462r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 8 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 0 2 3 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5468
  intro _
  exact s8_step5467 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5476 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5462 p8_5472r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 2 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5475
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5474

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5478 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5462 p8_5471r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 8 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5477
  intro _
  exact s8_step5476 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5484 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5461 p8_5480r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5483
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5482

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5486 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5461 p8_5479r := by
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5485
  intro _
  exact s8_step5484 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5488 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5320 p8_5460r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 0 0 <|
         Hubcap.one 3 1 <|
         Hubcap.one 4 3 <|
         Hubcap.one 6 5 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 5 7 8 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_5487
    intro _
    exact s8_step5486 hred
  intro _
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5478 hred
  intro _
  exact s8_step5469 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5496 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5460 p8_5492r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5495
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_5494

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5498 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5460 p8_5490r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 4 3 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5497
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step5496 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5500 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5320 p8_5458r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5499
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5498 hred
  intro _
  exact s8_step5488 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5502 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5320 p8_5456r := by
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 5 7 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_5501
  intro _
  exact s8_step5500 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5503 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_5037 p8_5037l := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step5502 hred
  intro L4_1
  exact s8_step5455 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step5504 (hred : RedpartSound theRedpart) :
    SucceedsIn q8_1 p8_1l := by
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
      · exact s8_step5503 hred
      intro L3_1
      refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 1 false L3_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s8_step5317 hred L3_1
    intro L2_1
    exact s8_step5036 hred L2_1
  intro L1_1
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s8_step2734 hred L1_1

end FourColor

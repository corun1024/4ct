import FourColor.Present10Step1
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 2 of the arity 10 presentation

A chunk of the case analysis of `present10.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step244 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L1_2 : Successful q10_16) :
    SucceedsIn q10_18 p10_236r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step243 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step254 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L2_1 : Successful q10_247)
    (L2_2 : Successful q10_249) :
    SucceedsIn q10_16 p10_251r := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_253

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step326 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L2_1 : Successful q10_247) :
    SucceedsIn q10_249 p10_249l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 5 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_325
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact h10_324 hred _
  intro _
  exact h10_266 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step327 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14)
    (L2_1 : Successful q10_247) :
    SucceedsIn q10_16 p10_247r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L2_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step326 hred L1_1 L2_1
  intro L2_2
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L2_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step254 hred L1_1 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step343 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_339r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_342
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_341

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step345 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_338r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_344
  intro _
  exact s10_step343 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step347 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_337r := by
  refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_346
  intro _
  exact s10_step345 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step349 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_335r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 3 6 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_348
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step347 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step351 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_334r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 3 8 <|
       Hubcap.two 4 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_350
  intro _
  exact s10_step349 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step358 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_355 p10_355l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_357

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step359 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_334 p10_354r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s10_step358 hred L1_1
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_356

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step361 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_334 p10_353r := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_360
  intro _
  exact s10_step359 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step363 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_333 p10_333l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_362

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step364 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_332r := by
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact s10_step363 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 9 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s10_step361 hred L1_1
  intro _
  exact s10_step351 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step366 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_332 p10_332l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_365

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step368 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_331 p10_331l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_367

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step380 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_377 p10_377l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_379

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step381 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_330 p10_376r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step380 hred L1_1
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 7 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_378

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step383 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_376 p10_376l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_382

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step385 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_375 p10_375l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_384

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step387 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_330 p10_373r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 5 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 3 9 <|
       Hubcap.two 6 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_386
  intro _
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact s10_step385 hred L1_1
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s10_step383 hred L1_1
  intro _
  exact s10_step381 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step389 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_373 p10_373l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_388

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step391 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_372 p10_372l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_390

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step393 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_371 p10_371l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_392

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step395 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_370 p10_370l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_394

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step396 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_330 p10_369r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s10_step395 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s10_step393 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact s10_step391 hred L1_1
  intro _
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact s10_step389 hred L1_1
  intro _
  exact s10_step387 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step411 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_247 p10_329r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact h10_410 hred _
    intro _
    exact s10_step396 hred L1_1
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s10_step368 hred L1_1
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s10_step366 hred L1_1
  intro _
  exact s10_step364 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step412 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_16 p10_245r := by
  refine succeed_by_split .spoke 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 8 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step411 hred L1_1
  intro L2_1
  exact s10_step327 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step413 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q10_14) :
    SucceedsIn q10_1 p10_15r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 false L1_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step412 hred L1_1
  intro L1_2
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 false L1_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 false L1_2
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step244 hred L1_1 L1_2
  intro _
  exact s10_step235 hred L1_1 L1_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step431 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418)
    (L3_1 : Successful q10_426) :
    SucceedsIn q10_420 p10_428r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_430

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step439 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_426 p10_435r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.two 1 9 6 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_438
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_437

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step441 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_435 p10_435l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_440

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step443 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_434 p10_434l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_442

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step445 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_426 p10_432r := by
  refine succeed_by_split .spoke 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_444
  intro _
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact s10_step443 hred L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step441 hred L2_1 L2_2 L2_3
  intro _
  exact s10_step439 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step447 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_432 p10_432l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_446

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step448 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_420 p10_425r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s10_step447 hred L2_1 L2_2 L2_3
    intro _
    exact s10_step445 hred L2_1 L2_2 L2_3
  intro L3_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step431 hred L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step450 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_420 p10_424r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 6 5 <|
       Hubcap.two 0 5 7 <|
       Hubcap.two 1 7 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_449
  intro _
  exact s10_step448 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step452 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_424 p10_424l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_451

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step454 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_423 p10_423l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_453

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step456 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L2_3 : Successful q10_418) :
    SucceedsIn q10_420 p10_420l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_455
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s10_step454 hred L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .spoke 8 7 false (by decide +kernel) ?_ ?_
  · exact s10_step452 hred L2_1 L2_2 L2_3
  intro _
  exact s10_step450 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step480 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_477 p10_477l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_479

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step481 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_476r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s10_step480 hred L2_1 L2_2
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_478

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step483 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_475 p10_475l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_482

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step485 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_474 p10_474l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_484

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step486 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_472r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s10_step485 hred L2_1 L2_2
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact s10_step483 hred L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step481 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step488 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_472 p10_472l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_487

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step490 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_468r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_489
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s10_step488 hred L2_1 L2_2
  intro _
  exact s10_step486 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step492 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_467r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_491
  intro _
  exact s10_step490 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step494 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_466r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_493
  intro _
  exact s10_step492 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step509 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_465 p10_505r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_508
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 7 8 7 <|
     Hubcap.two 7 9 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_507

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step511 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_465 p10_465l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_510
  intro _
  exact s10_step509 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step513 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_463r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 3 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_512
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step511 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact h10_504 hred _
  intro _
  exact s10_step494 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step517 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_463 p10_463l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 3 9 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_516
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_515

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step519 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_462 p10_462l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_518

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step521 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_461 p10_461l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_520

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step523 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_460 p10_460l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_522

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step524 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_459r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s10_step523 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 8 7 false (by decide +kernel) ?_ ?_
  · exact s10_step521 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 9 7 false (by decide +kernel) ?_ ?_
  · exact s10_step519 hred L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact s10_step517 hred L2_1 L2_2
  intro _
  exact s10_step513 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step536 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_418 p10_457r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 9 4 <|
       Hubcap.two 7 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_535
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact h10_534 hred _
  intro _
  exact s10_step524 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step557 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537)
    (L4_2 : Successful q10_553) :
    SucceedsIn q10_457 p10_553r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 false L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step565 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_553 p10_561r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_564
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_563

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step567 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_553 p10_560r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_566
  intro _
  exact s10_step565 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step569 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_553 p10_558r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_568
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step567 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step571 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_553 p10_553l := by
  refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_570
  intro _
  exact s10_step569 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step573 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_550r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_572
  intro _
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step571 hred L2_1 L2_2 L4_1
  intro L4_2
  exact s10_step557 hred L2_1 L2_2 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step575 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_549r := by
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.one 9 3 <|
       Hubcap.two 3 4 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_574
  intro _
  exact s10_step573 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step577 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_547r := by
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_576
  intro _
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step575 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step579 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_545r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_578
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step577 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step581 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_544r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_580
  intro _
  exact s10_step579 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step583 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_542r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_582
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step581 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step585 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_541r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_584
  intro _
  exact s10_step583 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step587 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_540r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_586
  intro _
  exact s10_step585 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step589 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_539r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_588
  intro _
  exact s10_step587 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step591 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416)
    (L4_1 : Successful q10_537) :
    SucceedsIn q10_457 p10_538r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_590
  intro _
  exact s10_step589 hred L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step605 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_601r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_604
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_603

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step607 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_599r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 5 <|
       Hubcap.one 9 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_606
  intro _
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step605 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step609 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_597r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_608
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step607 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step611 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_596r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_610
  intro _
  exact s10_step609 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step613 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_595r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.two 4 7 8 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_612
  intro _
  exact s10_step611 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step615 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_594r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_614
  intro _
  exact s10_step613 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step617 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_593r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_616
  intro _
  exact s10_step615 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step619 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_592r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_618
  intro _
  exact s10_step617 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step621 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_537 p10_537l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_620
  intro _
  exact s10_step619 hred L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step622 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L2_2 : Successful q10_416) :
    SucceedsIn q10_14 p10_417r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
      · exact s10_step621 hred L2_1 L2_2
      intro L4_1
      refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 5 false L4_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s10_step591 hred L2_1 L2_2 L4_1
    intro _
    exact s10_step536 hred L2_1 L2_2
  intro L2_3
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step456 hred L2_1 L2_2 L2_3
  intro L2_4
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step643 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_640 p10_640l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_642

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step644 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_639r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s10_step643 hred L2_1 L3_1 L3_2
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_641

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step646 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_638 p10_638l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_645

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step648 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_637 p10_637l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_647

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step650 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_635r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_649
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s10_step648 hred L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s10_step646 hred L2_1 L3_1 L3_2
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step644 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step658 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_631r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_657
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact h10_656 hred _
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step650 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step660 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_630r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_659
  intro _
  exact s10_step658 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step662 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_629r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_661
  intro _
  exact s10_step660 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step664 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_626 p10_628r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_663
  intro _
  exact s10_step662 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step665 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L3_2 : Successful q10_625) :
    SucceedsIn q10_416 p10_625r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 5 true L3_2
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step664 hred L2_1 L3_1 L3_2
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_627

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step693 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_689r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 3 9 <|
       Hubcap.two 5 6 8 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_692
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_691

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step695 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_689 p10_689l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_694

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step697 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_686r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_696
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact s10_step695 hred L2_1 L3_1
  intro _
  exact s10_step693 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step699 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_685r := by
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 4 <|
       Hubcap.one 9 4 <|
       Hubcap.two 1 3 9 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_698
  intro _
  exact s10_step697 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step701 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_682r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_700
  intro _
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step699 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step707 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_682 p10_703r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_706
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_705

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step709 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_702 p10_702l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_708

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step710 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_680r := by
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s10_step709 hred L2_1 L3_1
    intro _
    refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s10_step707 hred L2_1 L3_1
  intro _
  exact s10_step701 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step712 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_679r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_711
  intro _
  exact s10_step710 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step714 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_678r := by
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.one 9 3 <|
       Hubcap.two 0 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_713
  intro _
  exact s10_step712 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step716 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_676r := by
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_715
  intro _
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step714 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step718 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_674r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_717
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step716 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step720 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_673r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_719
  intro _
  exact s10_step718 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step722 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_672r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 3 5 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 4 8 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_721
  intro _
  exact s10_step720 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step727 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_672 p10_723r := by
  refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 3 5 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 7 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_726
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_725

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step729 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_723 p10_723l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_728

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step731 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_670r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_730
  intro _
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s10_step729 hred L2_1 L3_1
    intro _
    exact s10_step727 hred L2_1 L3_1
  intro _
  exact s10_step722 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step733 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_670 p10_670l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_732

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step735 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_669 p10_669l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_734

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step737 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_667r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_736
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s10_step735 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 8 7 false (by decide +kernel) ?_ ?_
  · exact s10_step733 hred L2_1 L3_1
  intro _
  exact s10_step731 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step739 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_625 p10_666r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_738
  intro _
  exact s10_step737 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step741 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_666 p10_666l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_740

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step771 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_768 p10_768l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_770

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step772 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_758 p10_767r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact s10_step771 hred L2_1 L3_1 L4_1
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 8 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_769

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step774 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_758 p10_765r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_773
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step772 hred L2_1 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step776 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_765 p10_765l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_775

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step778 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_763 p10_763l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_777

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step779 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_758 p10_761r := by
  refine succeed_by_split .hat 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 9 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s10_step778 hred L2_1 L3_1 L4_1
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact s10_step776 hred L2_1 L3_1 L4_1
  intro _
  exact s10_step774 hred L2_1 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step780 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_624 p10_757r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 false L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 3 false L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step779 hred L2_1 L3_1 L4_1
  intro L4_2
  refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 7 false L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_reducibility hred (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step782 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_624 p10_756r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_781
  intro _
  exact s10_step780 hred L2_1 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step784 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623)
    (L4_1 : Successful q10_754) :
    SucceedsIn q10_624 p10_755r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_783
  intro _
  exact s10_step782 hred L2_1 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step792 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_754 p10_788r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_791
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_790

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step794 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_754 p10_786r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_793
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s10_step792 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step796 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_754 p10_785r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_795
  intro _
  exact s10_step794 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step797 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_752r := by
  refine succeed_by_split .fan1 9 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s10_step796 hred L2_1 L3_1
  intro L4_1
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s10_step784 hred L2_1 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step799 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_751r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_798
  intro _
  exact s10_step797 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step801 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_751 p10_751l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.one 9 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_800

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step803 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_748r := by
  refine succeed_by_split .hat 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_802
  intro _
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 9 6 false (by decide +kernel) ?_ ?_
  · exact s10_step801 hred L2_1 L3_1
  intro _
  exact s10_step799 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step805 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_747r := by
  refine succeed_by_split .spoke 9 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_804
  intro _
  exact s10_step803 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step807 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_746r := by
  refine succeed_by_split .spoke 8 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 8 9 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_806
  intro _
  exact s10_step805 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step809 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_746 p10_746l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_808

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step811 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_745 p10_745l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_810

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step813 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_744 p10_744l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_812

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step815 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_743 p10_743l := by
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_814

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step816 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_624 p10_742r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s10_step815 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact s10_step813 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s10_step811 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s10_step809 hred L2_1 L3_1
  intro _
  exact s10_step807 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step817 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L3_1 : Successful q10_623) :
    SucceedsIn q10_416 p10_623r := by
  refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 false L3_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s10_step816 hred L2_1 L3_1
  intro _
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
    · exact s10_step741 hred L2_1 L3_1
    intro _
    exact s10_step739 hred L2_1 L3_1
  intro L3_2
  exact s10_step665 hred L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step823 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414)
    (L4_1 : Successful q10_820) :
    SucceedsIn q10_623 p10_820r := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_822

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step836 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414) :
    SucceedsIn q10_820 p10_820l := by
  refine succeed_by_split .spoke 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap10 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 8 <|
       Hubcap.two 8 9 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f10_835
  intro _
  exact h10_834 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step837 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q10_414) :
    SucceedsIn q10_416 p10_416l := by
  refine succeed_by_split .spoke 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 5 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 7 false L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 2 5 false (by decide +kernel) ?_ ?_
    · exact s10_step836 hred L2_1
    intro L4_1
    exact s10_step823 hred L2_1 L4_1
  intro L3_1
  exact s10_step817 hred L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s10_step861 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q10_838)
    (L3_2 : Successful q10_840)
    (L3_3 : Successful q10_842)
    (L3_4 : Successful q10_853) :
    SucceedsIn q10_414 p10_858r := by
  refine succeed_by_split .fan1 8 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap10 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f10_860

end FourColor

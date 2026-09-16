import FourColor.Present7Step8
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 9 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4298 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4230 p7_4230l := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4297 hred L1_1 L2_1 L4_1 L4_2
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4270 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4303 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4229 p7_4300r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4302

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4304 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226)
    (L4_2 : Successful q7_4228) :
    SucceedsIn q7_4107 p7_4228r := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step4303 hred L1_1 L2_1 L4_1 L4_2
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact s7_step4298 hred L1_1 L2_1 L4_1 L4_2
  intro _
  exact s7_step4256 hred L1_1 L2_1 L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4318 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4314r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4317
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4316

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4320 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4313r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4319
  intro _
  exact s7_step4318 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4326 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4313 p7_4322r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4325
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4324

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4328 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4313 p7_4321r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4327
  intro _
  exact s7_step4326 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4330 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4313 p7_4313l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4329
  intro _
  exact s7_step4328 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4339 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4311 p7_4335r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4338
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4337

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4341 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4311 p7_4334r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4340
  intro _
  exact s7_step4339 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4348 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4334 p7_4344r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4347
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4346

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4350 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4334 p7_4343r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4349
  intro _
  exact s7_step4348 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4352 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4334 p7_4342r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4351
  intro _
  exact s7_step4350 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4354 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4334 p7_4334l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4353
  intro _
  exact s7_step4352 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4360 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4332 p7_4356r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4359
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4358

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4362 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4332 p7_4355r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4361
  intro _
  exact s7_step4360 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4364 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4332 p7_4332l := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4363
  intro _
  exact s7_step4362 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4366 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4311 p7_4311l := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4365
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4364 hred L1_1 L2_1 L4_1
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact s7_step4354 hred L1_1 L2_1 L4_1
  intro _
  exact s7_step4341 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4369 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4310 p7_4310l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4368

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4370 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4309r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4369 hred L1_1 L2_1 L4_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4366 hred L1_1 L2_1 L4_1
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4330 hred L1_1 L2_1 L4_1
  intro _
  exact s7_step4320 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4375 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4309 p7_4372r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4374

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4381 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4308 p7_4378r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4380

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4382 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4307r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4381 hred L1_1 L2_1 L4_1
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4375 hred L1_1 L2_1 L4_1
  intro _
  exact s7_step4370 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4390 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4307 p7_4386r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4389
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4388

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4392 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4307 p7_4385r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4391
  intro _
  exact s7_step4390 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4394 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4307 p7_4384r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4393
  intro _
  exact s7_step4392 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4397 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4306 p7_4306l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4396

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4398 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4305r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4397 hred L1_1 L2_1 L4_1
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4394 hred L1_1 L2_1 L4_1
  intro _
  exact s7_step4382 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4407 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4305 p7_4403r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4406
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4405

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4409 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4305 p7_4402r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4408
  intro _
  exact s7_step4407 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4411 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4305 p7_4401r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4410
  intro _
  exact s7_step4409 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4412 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438)
    (L4_1 : Successful q7_4226) :
    SucceedsIn q7_4228 p7_4228l := by
  refine succeed_by_split .fan1 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 4 true L4_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4411 hred L1_1 L2_1 L4_1
  intro _
  exact s7_step4398 hred L1_1 L2_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4431 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4427r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4430
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4429

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4434 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4425r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.two 2 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4433
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4432
  intro _
  exact s7_step4431 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4439 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4425 p7_4435r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4438
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4437

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4441 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4425 p7_4425l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4440
  intro _
  exact s7_step4439 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4448 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4424 p7_4444r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4447
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4446

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4450 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4424 p7_4442r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4449
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4448 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4457 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4423 p7_4453r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4456
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4455

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4460 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4423 p7_4451r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4459
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.two 2 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4458
  intro _
  exact s7_step4457 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4461 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4422r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4460 hred L1_1 L2_1
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4450 hred L1_1 L2_1
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4441 hred L1_1 L2_1
  intro _
  exact s7_step4434 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4464 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4420r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4463
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 4 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4462
  intro _
  exact s7_step4461 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4471 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4420 p7_4467r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4470
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4469

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4476 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4467 p7_4472r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4475
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4474

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4478 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4467 p7_4467l := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4477
  intro _
  exact s7_step4476 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4480 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4420 p7_4465r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4479
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4478 hred L1_1 L2_1
  intro _
  exact s7_step4471 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4482 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4420 p7_4420l := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4481
  intro _
  exact s7_step4480 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4484 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4418r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4483
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step4482 hred L1_1 L2_1
  intro _
  exact s7_step4464 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4491 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4418 p7_4487r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4490
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4489

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4493 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4418 p7_4486r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4492
  intro _
  exact s7_step4491 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4495 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4416r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4494
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan2 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4493 hred L1_1 L2_1
  intro _
  exact s7_step4484 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4504 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4416 p7_4500r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4503
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4502

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4507 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4416 p7_4498r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4506
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4505
  intro _
  exact s7_step4504 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4509 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4416 p7_4496r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4508
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4507 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4511 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4414r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4510
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4509 hred L1_1 L2_1
  intro _
  exact s7_step4495 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4514 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_4226 p7_4226l := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4513
  intro _
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 6 (-1) <|
       Hubcap.two 2 5 4 <|
       Hubcap.two 3 4 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4512
  intro _
  exact s7_step4511 hred L1_1 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4515 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L2_1 : Successful q7_3438) :
    SucceedsIn q7_3440 p7_3440l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
    · exact s7_step4514 hred L1_1 L2_1
    intro L4_1
    refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact s7_step4412 hred L1_1 L2_1 L4_1
    intro L4_2
    exact s7_step4304 hred L1_1 L2_1 L4_1 L4_2
  intro L3_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4225 hred L1_1 L2_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4525 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L3_1 : Successful q7_4517) :
    SucceedsIn q7_3438 p7_4521r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4524

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4526 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L3_1 : Successful q7_4517) :
    SucceedsIn q7_3438 p7_4517r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4525 hred L1_1 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4539 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4517 p7_4535r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4538
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4537

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4541 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4517 p7_4532r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4540
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4539 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4554 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4531 p7_4550r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4553
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4552

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4557 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4531 p7_4548r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4556
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4555
  intro _
  exact s7_step4554 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4560 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4531 p7_4546r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4559
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4558
  intro _
  exact s7_step4557 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4562 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4531 p7_4545r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 1 5 3 <|
       Hubcap.two 3 5 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4561
  intro _
  exact s7_step4560 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4570 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4531 p7_4531l := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4569
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact h7_4568 hred _
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step4562 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4571 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4517 p7_4530r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step4570 hred L1_1
  intro _
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 5 2 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4542
  intro _
  exact s7_step4541 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4580 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4530 p7_4576r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4579
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4578

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4582 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4530 p7_4575r := by
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4581
  intro _
  exact s7_step4580 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4584 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4530 p7_4573r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4583
  intro _
  exact s7_step4582 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4591 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4529 p7_4587r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4590

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4592 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4517 p7_4528r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4591 hred L1_1
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step4584 hred L1_1
  intro _
  exact s7_step4571 hred L1_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step4606 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877) :
    SucceedsIn q7_4528 p7_4602r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_4605
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_4604

end FourColor

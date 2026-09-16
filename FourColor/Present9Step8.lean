import FourColor.Present9Step7
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 8 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3497 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3489r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3496
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3495 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3499 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3488r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3498
  intro _
  exact s9_step3497 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3501 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3487r := by
  refine succeed_by_split .spoke 0 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3500
  intro _
  exact s9_step3499 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3503 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3486r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3502
  intro _
  exact s9_step3501 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3505 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3485r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3504
  intro _
  exact s9_step3503 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3507 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3484r := by
  refine succeed_by_split .spoke 4 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 5 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3506
  intro _
  exact s9_step3505 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3509 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3410 p9_3483r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3508
  intro _
  exact s9_step3507 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3523 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3519r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3522
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3521

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3525 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3518r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3524
  intro _
  exact s9_step3523 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3527 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3516r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3526
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3525 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3529 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3515r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3528
  intro _
  exact s9_step3527 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3533 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3513 p9_3513l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 6 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3532
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3531

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3535 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3511r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3534
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact s9_step3533 hred L4_1
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3529 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3537 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3409 p9_3510r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3536
  intro _
  exact s9_step3535 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3538 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_3322 p9_3408r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3537 hred L4_1
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3509 hred L4_1
  intro _
  exact s9_step3482 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3539 (hred : RedpartSound theRedpart)
    (L4_1 : Successful q9_3320) :
    SucceedsIn q9_2541 p9_3321r := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3538 hred L4_1
  intro L4_2
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L4_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact s9_step3407 hred L4_1 L4_2
  intro _
  exact s9_step3369 hred L4_1 L4_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3558 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548)
    (L5_3 : Successful q9_3550) :
    SucceedsIn q9_3320 p9_3554r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3557
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3556

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3560 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548)
    (L5_3 : Successful q9_3550) :
    SucceedsIn q9_3320 p9_3553r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3559
  intro _
  exact s9_step3558 hred L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3570 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548)
    (L6_1 : Successful q9_3565) :
    SucceedsIn q9_3550 p9_3567r := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3569

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3572 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548)
    (L6_1 : Successful q9_3565) :
    SucceedsIn q9_3550 p9_3565r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 3 5 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3571
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3570 hred L5_1 L5_2 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3576 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3565 p9_3565l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3575
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3574

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3584 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3564 p9_3580r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 6 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3583
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3582

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3586 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3564 p9_3578r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 6 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3585
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3584 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3588 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3564 p9_3564l := by
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3587
  intro _
  exact s9_step3586 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3590 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3550 p9_3562r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3589
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact s9_step3588 hred L5_1 L5_2
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3576 hred L5_1 L5_2
  intro L6_1
  exact s9_step3572 hred L5_1 L5_2 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3592 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3550 p9_3561r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3591
  intro _
  exact s9_step3590 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3594 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544)
    (L5_2 : Successful q9_3548) :
    SucceedsIn q9_3320 p9_3549r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap9 hred
        (Hubcap.one 4 3 <|
         Hubcap.one 6 5 <|
         Hubcap.one 8 4 <|
         Hubcap.two 0 7 6 <|
         Hubcap.two 1 2 4 <|
         Hubcap.two 3 5 8 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f9_3593
    intro _
    exact s9_step3592 hred L5_1 L5_2
  intro L5_3
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3560 hred L5_1 L5_2 L5_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3610 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3606r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3609
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3608

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3612 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3604r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 6 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3611
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3610 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3614 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3603r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3613
  intro _
  exact s9_step3612 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3616 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3602r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3615
  intro _
  exact s9_step3614 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3618 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3601r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3617
  intro _
  exact s9_step3616 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3620 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3600r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3619
  intro _
  exact s9_step3618 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3622 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3599r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3621
  intro _
  exact s9_step3620 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3624 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3598r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3623
  intro _
  exact s9_step3622 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3629 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3598 p9_3625r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 7 6 <|
       Hubcap.two 1 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3628
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3627

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3631 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3548 p9_3596r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3630
  intro _
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3629 hred L5_1
  intro _
  exact s9_step3624 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3632 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3320 p9_3547r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3631 hred L5_1
  intro L5_2
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3594 hred L5_1 L5_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3634 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3320 p9_3546r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3633
  intro _
  exact s9_step3632 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3636 (hred : RedpartSound theRedpart)
    (L5_1 : Successful q9_3544) :
    SucceedsIn q9_3320 p9_3545r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3635
  intro _
  exact s9_step3634 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3653 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3649r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3652
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3651

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3655 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3648r := by
  refine succeed_by_split .hat 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3654
  intro _
  exact s9_step3653 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3657 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3647r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3656
  intro _
  exact s9_step3655 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3659 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3646r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3658
  intro _
  exact s9_step3657 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3661 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3643r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 5 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3660
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3659 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3662 (hred : RedpartSound theRedpart)
    (L6_1 : Successful q9_3639) :
    SucceedsIn q9_3544 p9_3639r := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3661 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3668 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3639 p9_3664r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3667
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3666

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3670 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3639 p9_3663r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3669
  intro _
  exact s9_step3668 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3672 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3639 p9_3639l := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3671
  intro _
  exact s9_step3670 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3674 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3544 p9_3637r := by
  refine succeed_by_split .spoke 3 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3673
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s9_step3672 hred
  intro L6_1
  exact s9_step3662 hred L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3676 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3320 p9_3542r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3675
  intro _
  refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3674 hred
  intro L5_1
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 5 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3636 hred L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3678 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_3320 p9_3541r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 5 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 3 4 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3677
  intro _
  exact s9_step3676 hred

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3679 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_2541 p9_2541l := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step3678 hred
  intro L4_1
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step3539 hred L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3680 (hred : RedpartSound theRedpart) :
    SucceedsIn q9_1 p9_1l := by
  refine succeed_by_split .spoke 7 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
      · exact s9_step3679 hred
      intro L3_1
      refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 1 false L3_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s9_step3319 hred L3_1
    intro L2_1
    exact s9_step2540 hred L2_1
  intro L1_1
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 1 false L1_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step791 hred L1_1

end FourColor

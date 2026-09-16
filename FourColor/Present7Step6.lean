import FourColor.Present7Step5
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 6 of the arity 7 presentation

A chunk of the case analysis of `present7.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2480 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2399 p7_2399l := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.two 1 3 1 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2479
  intro _
  exact s7_step2478 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2481 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2276 p7_2398r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact s7_step2480 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2471 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2453 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  exact s7_step2437 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2493 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2398 p7_2489r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2492
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2491

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2496 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2398 p7_2487r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2495
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2494
  intro _
  exact s7_step2493 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2499 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2398 p7_2485r := by
  refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2498
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2497
  intro _
  exact s7_step2496 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2504 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2484 p7_2484l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2503
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2502

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2505 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2398 p7_2483r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2504 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2500
  intro _
  exact s7_step2499 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2512 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2483 p7_2507r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2511
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2510

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2514 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2483 p7_2483l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2513
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2512 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2520 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2482 p7_2516r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2519
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2518

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2523 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2482 p7_2482l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2522
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2521
  intro _
  exact s7_step2520 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2524 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_1824 p7_2275r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
      · exact s7_step2523 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
      intro _
      refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
      · exact s7_step2514 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
      intro _
      exact s7_step2505 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
    intro _
    exact s7_step2481 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro L3_1
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2397 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1
  intro _
  exact s7_step2317 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L3_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2535 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2275 p7_2531r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2534
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2533

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2537 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2275 p7_2529r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 4 6 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2536
  intro _
  exact s7_step2535 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2539 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2275 p7_2527r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2538
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2537 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2551 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L5_1 : Successful q7_2541) :
    SucceedsIn q7_2526 p7_2547r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2550
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2549

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2553 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L5_1 : Successful q7_2541) :
    SucceedsIn q7_2526 p7_2545r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 6 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2552
  intro _
  exact s7_step2551 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2555 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823)
    (L5_1 : Successful q7_2541) :
    SucceedsIn q7_2526 p7_2543r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2554
  intro _
  exact s7_step2553 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2562 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2541 p7_2557r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2561
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2560

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2564 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2541 p7_2541l := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2563
  intro _
  exact s7_step2562 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2566 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2526 p7_2526l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2565
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2564 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro L5_1
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2555 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2575 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2525 p7_2571r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2574
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2573

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2578 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2525 p7_2569r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2577
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2576
  intro _
  exact s7_step2575 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2584 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2568 p7_2579r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2583
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2582

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2586 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2525 p7_2567r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 1 3 4 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2585
    intro _
    exact s7_step2584 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2578 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2588 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2275 p7_2275l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 3 0 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 4 5 3 <|
         Hubcap.two 4 6 4 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2587
    intro _
    exact s7_step2586 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s7_step2566 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2539 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2597 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2274 p7_2593r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2596
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2595

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2600 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2274 p7_2591r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2599
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2598
  intro _
  exact s7_step2597 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2606 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2591 p7_2602r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2605
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2604

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2609 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2591 p7_2591l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2608
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2607
  intro _
  exact s7_step2606 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2613 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_2590 p7_2590l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 6 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2612
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2611

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2614 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L2_3 : Successful q7_1823) :
    SucceedsIn q7_1824 p7_1824l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_3
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2613 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
    intro _
    refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2609 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
    intro _
    exact s7_step2600 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2588 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro _
  exact s7_step2524 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2628 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1823 p7_2624r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2627
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2626

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2632 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2623 p7_2623l := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2631
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2630

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2638 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2622 p7_2634r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2637
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2636

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2641 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2622 p7_2622l := by
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2640
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 5 0 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2639
  intro _
  exact s7_step2638 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2652 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2621 p7_2648r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2651
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2650

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2655 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2621 p7_2646r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2654
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2653
  intro _
  exact s7_step2652 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2657 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2621 p7_2644r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2656
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2655 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2660 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2621 p7_2642r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 3 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2659
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2658
  intro _
  exact s7_step2657 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2662 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1823 p7_2620r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 0 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 3 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2661
    intro _
    exact s7_step2660 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact s7_step2641 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2632 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .fan2 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2628 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2666 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2620 p7_2620l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2665
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 6 1 <|
     Hubcap.two 0 5 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2664

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2672 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2619 p7_2668r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2671
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2670

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2675 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2619 p7_2619l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2674
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2673
  intro _
  exact s7_step2672 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2682 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2618 p7_2678r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2681
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2680

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2685 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2618 p7_2676r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2684
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2683
  intro _
  exact s7_step2682 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2687 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1823 p7_2617r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 3 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 0 5 2 <|
         Hubcap.two 2 3 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2686
    intro _
    exact s7_step2685 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2675 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2666 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  exact s7_step2662 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2692 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2617 p7_2688r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 1 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2691
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2690

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2699 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2616 p7_2695r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 6 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2698
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2697

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2703 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2694 p7_2694l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2702
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2701

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2710 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2693 p7_2706r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2709
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2708

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2712 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2693 p7_2705r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2711
  intro _
  exact s7_step2710 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2715 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2693 p7_2693l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2714
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2713
  intro _
  exact s7_step2712 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2716 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1823 p7_2615r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2715 hred L1_1 L1_2 L1_3 L2_1 L2_2
    intro _
    refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2703 hred L1_1 L1_2 L1_3 L2_1 L2_2
    intro _
    refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2699 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2692 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  exact s7_step2687 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2726 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L4_1 : Successful q7_2717) :
    SucceedsIn q7_2615 p7_2722r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2725
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2724

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2728 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L4_1 : Successful q7_2717) :
    SucceedsIn q7_2615 p7_2720r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2727
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2726 hred L1_1 L1_2 L1_3 L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2731 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L4_1 : Successful q7_2717) :
    SucceedsIn q7_2615 p7_2718r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2730
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2729
  intro _
  exact s7_step2728 hred L1_1 L1_2 L1_3 L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2737 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L4_1 : Successful q7_2717) :
    SucceedsIn q7_2718 p7_2733r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2736
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2735

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2739 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821)
    (L4_1 : Successful q7_2717) :
    SucceedsIn q7_2718 p7_2732r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2738
  intro _
  exact s7_step2737 hred L1_1 L1_2 L1_3 L2_1 L2_2 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2743 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2717 p7_2717l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2742
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2741

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2744 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1823 p7_1823l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2743 hred L1_1 L1_2 L1_3 L2_1 L2_2
    intro L4_1
    refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 6 true L4_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s7_step2739 hred L1_1 L1_2 L1_3 L2_1 L2_2 L4_1
    intro _
    exact s7_step2731 hred L1_1 L1_2 L1_3 L2_1 L2_2 L4_1
  intro _
  exact s7_step2716 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2756 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1822 p7_2752r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2755
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2754

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2758 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1822 p7_2750r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 1 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2757
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2756 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2765 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2749 p7_2761r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 (-1) <|
       Hubcap.one 5 2 <|
       Hubcap.two 1 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2764
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 2 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2763

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2768 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2749 p7_2749l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2767
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2766
  intro _
  exact s7_step2765 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2769 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1822 p7_2748r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2768 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 1 5 4 <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2759
  intro _
  exact s7_step2758 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2786 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2782r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2785
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2784

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2788 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2780r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2787
  intro _
  refine succeed_by_split .fan2 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2786 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2790 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2779r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2789
  intro _
  exact s7_step2788 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2792 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2778r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2791
  intro _
  exact s7_step2790 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2794 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2776r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2793
  intro _
  exact s7_step2792 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2796 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2774r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2795
  intro _
  exact s7_step2794 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2799 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2772r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 5 4 <|
       Hubcap.two 1 3 2 <|
       Hubcap.two 2 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2798
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2797
  intro _
  exact s7_step2796 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2807 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2771 p7_2803r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2806
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2805

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2810 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2771 p7_2801r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 4 0 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2809
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 3 4 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2808
  intro _
  exact s7_step2807 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2812 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2747 p7_2747l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.one 5 2 <|
         Hubcap.one 6 2 <|
         Hubcap.two 1 2 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2811
    intro _
    exact s7_step2810 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 1 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2800
  intro _
  exact s7_step2799 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2813 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_1822 p7_2746r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2812 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 0 5 5 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2770
  intro _
  exact s7_step2769 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2823 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2746 p7_2819r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2822
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2821

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2825 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2746 p7_2817r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 6 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2824
  intro _
  exact s7_step2823 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2828 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2746 p7_2815r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 1 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2827
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2826
  intro _
  exact s7_step2825 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2832 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2815 p7_2815l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 3 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2831
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2830

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2834 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_2746 p7_2746l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2833
  intro _
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact s7_step2832 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  exact s7_step2828 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2835 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819)
    (L2_2 : Successful q7_1821) :
    SucceedsIn q7_883 p7_1821r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_2
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact s7_step2834 hred L1_1 L1_2 L1_3 L2_1 L2_2
    intro _
    exact s7_step2813 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s7_step2744 hred L1_1 L1_2 L1_3 L2_1 L2_2
  intro L2_3
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s7_step2614 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3
  intro L2_4
  exact s7_step2273 hred L1_1 L1_2 L1_3 L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2848 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1821 p7_2844r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-1) <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2847
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 (-1) <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2846

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2852 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2844 p7_2844l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2851
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2850

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2854 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1821 p7_2842r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2853
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2852 hred L1_1 L1_2 L1_3 L2_1
  intro _
  exact s7_step2848 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2863 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2841 p7_2859r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2862
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2861

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2869 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2858 p7_2865r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2868
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2867

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2871 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2841 p7_2857r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 4 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 (-1) <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2870
    intro _
    exact s7_step2869 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 (-1) <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2864
  intro _
  exact s7_step2863 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2874 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2841 p7_2841l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2873
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2872
  intro _
  exact s7_step2871 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2875 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1821 p7_2840r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2874 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 5 4 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2855
  intro _
  exact s7_step2854 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2881 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2840 p7_2877r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 1 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2880
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2879

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2883 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2840 p7_2840l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 1 <|
       Hubcap.two 1 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2882
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2881 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2889 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2839 p7_2885r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2888
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2887

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2891 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2839 p7_2884r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2890
  intro _
  exact s7_step2889 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2898 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2838 p7_2894r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2897
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2896

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2902 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2894 p7_2894l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2901
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2900

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2904 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2838 p7_2892r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2903
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2902 hred L1_1 L1_2 L1_3 L2_1
  intro _
  exact s7_step2898 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2906 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1821 p7_2837r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 3 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 0 <|
         Hubcap.two 5 6 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2905
    intro _
    exact s7_step2904 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step2891 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact s7_step2883 hred L1_1 L1_2 L1_3 L2_1
  intro _
  exact s7_step2875 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2923 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2919r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.two 4 5 2 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2922
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2921

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2926 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2917r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2925
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 (-1) <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2924
  intro _
  exact s7_step2923 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2928 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2915r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2927
  intro _
  exact s7_step2926 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2930 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2913r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 3 (-1) <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2929
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2928 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2933 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2911r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2932
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 (-1) <|
       Hubcap.one 4 0 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2931
  intro _
  exact s7_step2930 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2939 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2911 p7_2935r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2938
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2937

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2942 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2911 p7_2911l := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2941
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2940
  intro _
  exact s7_step2939 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2944 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2909r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2943
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2942 hred L1_1 L1_2 L1_3 L2_1
  intro _
  exact s7_step2933 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2947 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2836 p7_2836l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2946
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 0 <|
       Hubcap.two 1 4 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2945
  intro _
  exact s7_step2944 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2948 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1821 p7_1821l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2947 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 5 3 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2907
  intro _
  exact s7_step2906 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2961 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1820 p7_2957r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2960
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2959

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2964 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1820 p7_2955r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 4 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2963
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2962
  intro _
  exact s7_step2961 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2968 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2955 p7_2955l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2967
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2966

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2970 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1820 p7_2953r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2969
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s7_step2968 hred L1_1 L1_2 L1_3 L2_1
  intro _
  exact s7_step2964 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2982 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2952 p7_2978r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2981
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_2980

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2984 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2952 p7_2976r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2983
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step2982 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2986 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2952 p7_2975r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2985
  intro _
  exact s7_step2984 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2988 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2952 p7_2974r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2987
  intro _
  exact s7_step2986 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2991 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_2952 p7_2972r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2990
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 6 0 <|
       Hubcap.two 0 3 3 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2989
  intro _
  exact s7_step2988 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2993 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1820 p7_2951r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 2 0 <|
         Hubcap.one 6 0 <|
         Hubcap.two 1 3 5 <|
         Hubcap.two 4 5 2 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_2992
    intro _
    exact s7_step2991 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 3 3 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2971
  intro _
  exact s7_step2970 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step2996 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881)
    (L2_1 : Successful q7_1819) :
    SucceedsIn q7_1820 p7_2949r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2995
  intro _
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_2994
  intro _
  exact s7_step2993 hred L1_1 L1_2 L1_3 L2_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3018 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3014r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3017
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3016

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3020 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3013r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3019
  intro _
  exact s7_step3018 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3022 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3011r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3021
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3020 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3031 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3010 p7_3027r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3030
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3034 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3010 p7_3025r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3033
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3032
  intro _
  exact s7_step3031 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3036 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3010 p7_3024r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3035
  intro _
  exact s7_step3034 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3038 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3009r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 3 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 4 5 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3037
    intro _
    exact s7_step3036 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 3 <|
       Hubcap.two 4 5 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3023
  intro _
  exact s7_step3022 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3040 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3007r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3039
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3038 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3043 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3005r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3042
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3041
  intro _
  exact s7_step3040 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3049 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3004 p7_3045r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3048
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3047

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3051 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3003r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.two 3 4 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3050
    intro _
    exact s7_step3049 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3044
  intro _
  exact s7_step3043 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3054 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_3001r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3053
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3052
  intro _
  exact s7_step3051 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3064 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3001 p7_3060r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3063
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3062

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3067 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3001 p7_3058r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3066
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 3 2 <|
       Hubcap.two 2 5 3 <|
       Hubcap.two 4 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3065
  intro _
  exact s7_step3064 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3070 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3001 p7_3056r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 4 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3069
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3068
  intro _
  exact s7_step3067 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3073 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3001 p7_3001l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3072
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3071
  intro _
  exact s7_step3070 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3075 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_2999r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3074
  intro _
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact s7_step3073 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3054 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3092 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3088r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3091
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3090

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3095 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3086r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3094
  intro _
  refine succeed_by_split .hat 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3093
  intro _
  exact s7_step3092 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3097 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3084r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3096
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3095 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3103 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3083 p7_3099r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3102
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3101

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3105 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3082r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 2 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 2 <|
         Hubcap.two 3 4 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3104
    intro _
    exact s7_step3103 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3098
  intro _
  exact s7_step3097 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3110 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3082 p7_3106r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3109
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3108

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3112 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3080r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 4 3 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3111
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3110 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3105 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3117 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3080 p7_3113r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 1 0 <|
       Hubcap.two 0 4 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3116
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3115

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3119 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3079r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 2 <|
         Hubcap.one 1 0 <|
         Hubcap.one 4 2 <|
         Hubcap.one 5 0 <|
         Hubcap.one 6 3 <|
         Hubcap.two 2 3 3 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3118
    intro _
    exact s7_step3117 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3112 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3126 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3079 p7_3122r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3125
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3124

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3132 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3121 p7_3128r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3131
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3130

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3134 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3079 p7_3120r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 2 <|
         Hubcap.one 4 0 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3133
    intro _
    exact s7_step3132 hred L1_1 L1_2 L1_3
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.two 3 5 4 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3127
  intro _
  exact s7_step3126 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3136 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3078r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 4 0 <|
         Hubcap.one 6 3 <|
         Hubcap.two 3 5 4 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3135
    intro _
    exact s7_step3134 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3119 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3143 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3078 p7_3139r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3142
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3141

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3146 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3078 p7_3137r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3145
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 2 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3144
  intro _
  exact s7_step3143 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3148 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_2999 p7_3077r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.two 5 6 3 <|
         Hubcap.two 0 3 6 <|
         Hubcap.two 0 4 4 <|
         Hubcap.two 3 4 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3147
    intro _
    exact s7_step3146 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3136 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3154 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3077 p7_3150r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 2 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3153
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3152

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3157 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3077 p7_3077l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3156
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 5 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3155
  intro _
  exact s7_step3154 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3163 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3076 p7_3159r := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3162
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3161

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3166 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_3076 p7_3076l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3165
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 4 0 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 5 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3164
  intro _
  exact s7_step3163 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3168 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_1819 p7_2997r := by
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 0 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3167
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
    · exact s7_step3166 hred L1_1 L1_2 L1_3
    intro _
    refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
    · exact s7_step3157 hred L1_1 L1_2 L1_3
    intro _
    exact s7_step3148 hred L1_1 L1_2 L1_3
  intro _
  exact s7_step3075 hred L1_1 L1_2 L1_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3170 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L1_3 : Successful q7_881) :
    SucceedsIn q7_883 p7_883l := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap7 hred
        (Hubcap.one 0 3 <|
         Hubcap.one 1 0 <|
         Hubcap.one 2 0 <|
         Hubcap.one 3 0 <|
         Hubcap.one 4 2 <|
         Hubcap.two 5 6 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f7_3169
    intro _
    exact s7_step3168 hred L1_1 L1_2 L1_3
  intro L2_1
  refine succeed_by_split .spoke 6 7 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_similarity 6 true L2_1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    intro _
    exact s7_step2996 hred L1_1 L1_2 L1_3 L2_1
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact s7_step2948 hred L1_1 L1_2 L1_3 L2_1
  intro L2_2
  exact s7_step2835 hred L1_1 L1_2 L1_3 L2_1 L2_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3187 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175)
    (L2_3 : Successful q7_3179) :
    SucceedsIn q7_881 p7_3183r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3186
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3185

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3189 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175)
    (L2_3 : Successful q7_3179) :
    SucceedsIn q7_881 p7_3182r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3188
  intro _
  exact s7_step3187 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3191 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175)
    (L2_3 : Successful q7_3179) :
    SucceedsIn q7_881 p7_3181r := by
  refine succeed_by_split .spoke 1 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3190
  intro _
  exact s7_step3189 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3193 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175)
    (L2_3 : Successful q7_3179) :
    SucceedsIn q7_881 p7_3179r := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 2 <|
       Hubcap.two 1 2 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3192
  intro _
  exact s7_step3191 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3197 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175) :
    SucceedsIn q7_3179 p7_3194r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3196

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3198 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L2_2 : Successful q7_3175) :
    SucceedsIn q7_881 p7_3176r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step3197 hred L1_1 L1_2 L2_1 L2_2
  intro L2_3
  exact s7_step3193 hred L1_1 L1_2 L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3209 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199)
    (L3_2 : Successful q7_3202) :
    SucceedsIn q7_3175 p7_3205r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3208
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3207

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3211 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199)
    (L3_2 : Successful q7_3202) :
    SucceedsIn q7_3175 p7_3203r := by
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 (-1) <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.two 5 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3210
  intro _
  exact s7_step3209 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3220 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199)
    (L3_2 : Successful q7_3202) :
    SucceedsIn q7_3203 p7_3216r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3219
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3218

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3222 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199)
    (L3_2 : Successful q7_3202) :
    SucceedsIn q7_3203 p7_3213r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.one 6 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3221
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step3220 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3224 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199)
    (L3_2 : Successful q7_3202) :
    SucceedsIn q7_3203 p7_3203l := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 6 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3223
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step3222 hred L1_1 L1_2 L2_1 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s7_step3229 (hred : RedpartSound theRedpart)
    (L1_1 : Successful q7_877)
    (L1_2 : Successful q7_879)
    (L2_1 : Successful q7_3172)
    (L3_1 : Successful q7_3199) :
    SucceedsIn q7_3202 p7_3225r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-1) <|
       Hubcap.one 6 2 <|
       Hubcap.two 0 1 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_3228
  intro _
  exact succeed_by_hubcap7 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f7_3227

end FourColor

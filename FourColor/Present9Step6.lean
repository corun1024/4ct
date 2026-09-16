import FourColor.Present9Step5
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 6 of the arity 9 presentation

A chunk of the case analysis of `present9.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2641 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2629r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2640
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2639 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2651 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2626 p9_2647r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 5 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2650
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2649

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2653 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2626 p9_2646r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 2 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2652
  intro _
  exact s9_step2651 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2655 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2626 p9_2644r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2654
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2653 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2657 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2626 p9_2626l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2656
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2655 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2658 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2625r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2657 hred L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2641 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2660 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2624r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2659
  intro _
  exact s9_step2658 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2662 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2622r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2661
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2660 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2664 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2621r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2663
  intro _
  exact s9_step2662 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2666 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2620r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2665
  intro _
  exact s9_step2664 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2668 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2619r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2667
  intro _
  exact s9_step2666 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2670 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2618r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2669
  intro _
  exact s9_step2668 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2672 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2617r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2671
  intro _
  exact s9_step2670 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2674 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2616r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2673
  intro _
  exact s9_step2672 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2693 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543)
    (L5_1 : Successful q9_2686) :
    SucceedsIn q9_2615 p9_2689r := by
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2692

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2699 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2686 p9_2695r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.two 5 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2698
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2697

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2701 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2686 p9_2686l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2700
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2699 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2702 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2685r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2701 hred L3_1 L3_2
  intro L5_1
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L5_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2693 hred L3_1 L3_2 L5_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2704 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2684r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2703
  intro _
  exact s9_step2702 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2706 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2683r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2705
  intro _
  exact s9_step2704 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2708 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2682r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2707
  intro _
  exact s9_step2706 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2710 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2681r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2709
  intro _
  exact s9_step2708 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2712 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2680r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2711
  intro _
  exact s9_step2710 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2714 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2679r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2713
  intro _
  exact s9_step2712 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2716 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2678r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2715
  intro _
  exact s9_step2714 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2718 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2677r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2717
  intro _
  exact s9_step2716 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2720 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2676r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2719
  intro _
  exact s9_step2718 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2722 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2615 p9_2615l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2721
  intro _
  exact s9_step2720 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2723 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L3_2 : Successful q9_2543) :
    SucceedsIn q9_2545 p9_2545l := by
  refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
  · exact s9_step2722 hred L3_1 L3_2
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2675
  intro _
  exact s9_step2674 hred L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2753 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2749r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2752
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2751

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2755 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2747r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 8 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2754
  intro _
  exact s9_step2753 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2757 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2746r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2756
  intro _
  exact s9_step2755 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2768 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2764r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2767
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2766

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2770 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2763r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2769
  intro _
  exact s9_step2768 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2772 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2762r := by
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2771
  intro _
  exact s9_step2770 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2774 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2761r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2773
  intro _
  exact s9_step2772 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2777 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2759r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2776
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2775
  intro _
  exact s9_step2774 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2779 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2744 p9_2744l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2778
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2777 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2780 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2742r := by
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2779 hred L3_1 L4_1
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2757 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2782 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2741r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2781
  intro _
  exact s9_step2780 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2784 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2739r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2783
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2782 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2786 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2738r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2785
  intro _
  exact s9_step2784 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2788 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2737r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2787
  intro _
  exact s9_step2786 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2790 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2736r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2789
  intro _
  exact s9_step2788 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2793 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2734r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2792
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2791
  intro _
  exact s9_step2790 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2814 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2810r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 3 6 <|
       Hubcap.two 1 2 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2813
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2812

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2816 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2809r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2815
  intro _
  exact s9_step2814 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2818 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2807r := by
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2817
  intro _
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2816 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2820 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2804r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 7 9 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2819
  intro _
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2818 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2822 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2802r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2821
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2820 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2824 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2800r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2823
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2822 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2826 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2798r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 8 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2825
  intro _
  refine succeed_by_split .fan2 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2824 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2828 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2797r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 3 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 7 <|
       Hubcap.two 1 2 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2827
  intro _
  exact s9_step2826 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2830 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2796r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2829
  intro _
  exact s9_step2828 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2832 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2795r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2831
  intro _
  exact s9_step2830 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2834 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2794r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2833
  intro _
  exact s9_step2832 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2836 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2733 p9_2733l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 0 8 6 <|
       Hubcap.two 1 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2835
  intro _
  exact s9_step2834 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2850 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2846r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2849
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2848

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2852 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2845r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2851
  intro _
  exact s9_step2850 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2864 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2860r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2863
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2862

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2866 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2858r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 5 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2865
  intro _
  exact s9_step2864 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2868 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2856r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2867
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2866 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2870 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2855r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 7 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2869
  intro _
  exact s9_step2868 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2873 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2853r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2872
  intro _
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2871
  intro _
  exact s9_step2870 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2875 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2844 p9_2844l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2874
  intro _
  exact s9_step2873 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2877 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2841r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2876
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 false (by decide +kernel) ?_ ?_
  · exact s9_step2875 hred L3_1 L4_1
  intro _
  refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2852 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2879 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2840r := by
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2878
  intro _
  exact s9_step2877 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2882 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2838r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2881
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 6 6 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2880
  intro _
  exact s9_step2879 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2885 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2732 p9_2732l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 7 5 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2884
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2883
  intro _
  exact s9_step2882 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2887 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2730r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2886
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2885 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s9_step2836 hred L3_1 L4_1
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2793 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2889 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2729r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 1 2 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2888
  intro _
  exact s9_step2887 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2891 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2728r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2890
  intro _
  exact s9_step2889 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2893 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2727r := by
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2892
  intro _
  exact s9_step2891 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2895 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2543 p9_2726r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2894
  intro _
  exact s9_step2893 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2901 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L5_1 : Successful q9_2896) :
    SucceedsIn q9_2726 p9_2897r := by
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.two 0 5 9 <|
     Hubcap.two 0 7 9 <|
     Hubcap.two 5 7 9 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2900

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2918 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2896 p9_2914r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 5 8 <|
       Hubcap.two 2 6 5 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2917
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2916

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2923 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2914 p9_2919r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2922
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2921

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2925 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2914 p9_2914l := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2924
  intro _
  exact s9_step2923 hred L3_1 L4_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2927 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2896 p9_2912r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2926
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s9_step2925 hred L3_1 L4_1 L6_1
  intro _
  exact s9_step2918 hred L3_1 L4_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2929 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2896 p9_2911r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 5 8 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2928
  intro _
  exact s9_step2927 hred L3_1 L4_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2945 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2909 p9_2936r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact h9_2944 hred _
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 5 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2938

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2946 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724)
    (L6_1 : Successful q9_2907) :
    SucceedsIn q9_2896 p9_2908r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s9_step2945 hred L3_1 L4_1 L6_1
  intro _
  refine succeed_by_split .hat 8 5 false (by decide +kernel) ?_ ?_
  · exact h9_2935 hred _
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 3 true L6_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s9_step2929 hred L3_1 L4_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2962 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2907 p9_2958r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2961
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2960

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2964 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2907 p9_2956r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 6 <|
       Hubcap.two 2 3 6 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2963
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step2962 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2966 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2907 p9_2955r := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 4 6 <|
       Hubcap.two 3 5 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2965
  intro _
  exact s9_step2964 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2970 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2955 p9_2955l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.two 4 5 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2969
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2968

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2971 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2896 p9_2906r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 8 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
    · exact s9_step2970 hred L3_1 L4_1
    intro _
    exact s9_step2966 hred L3_1 L4_1
  intro L6_1
  refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
  · exact h9_2952 hred _
  intro _
  exact s9_step2946 hred L3_1 L4_1 L6_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2985 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2905 p9_2905l := by
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2984
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2983

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2987 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2896 p9_2903r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 7 5 <|
       Hubcap.two 6 8 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2986
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact s9_step2985 hred L3_1 L4_1
  intro _
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact h9_2981 hred _
  intro _
  exact s9_step2971 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2989 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2896 p9_2902r := by
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.two 0 1 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2988
  intro _
  exact s9_step2987 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step2991 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2896 p9_2896l := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_2990
  intro _
  exact s9_step2989 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3013 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3009r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 4 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3012
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3011

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3015 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3007r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 3 4 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3014
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3013 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3017 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3006r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 1 4 5 <|
       Hubcap.two 3 5 8 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3016
  intro _
  exact s9_step3015 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3019 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3005r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3018
  intro _
  exact s9_step3017 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3021 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3003r := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3020
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3019 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3023 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_2725 p9_3002r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 5 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3022
  intro _
  exact s9_step3021 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3033 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3002 p9_3029r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 5 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3032
  intro _
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3031

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3035 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3002 p9_3027r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 2 8 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3034
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s9_step3033 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3037 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3002 p9_3026r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.two 5 8 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3036
  intro _
  exact s9_step3035 hred L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s9_step3039 (hred : RedpartSound theRedpart)
    (L3_1 : Successful q9_2541)
    (L4_1 : Successful q9_2724) :
    SucceedsIn q9_3002 p9_3025r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap9 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 5 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 5 <|
       Hubcap.one 8 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f9_3038
  intro _
  exact s9_step3037 hred L3_1 L4_1

end FourColor

import FourColor.Present9Hub4

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap steps 5 of the arity 9 presentation

A `Hubcap` step of the script whose check was too large for one computation,
as a case analysis finer than the reference's with the same hubcap applied in
each branch. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2512 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2510l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2511

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2515 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2513l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2514

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2518 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2516l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2517

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2520 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2516r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2519

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2521 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2513r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h9_2518 hred _
  intro _
  exact h9_2520 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2522 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2510r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_2515 hred _
  intro _
  exact h9_2521 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2523 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2439l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_2512 hred _
  intro _
  exact h9_2522 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2527 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2525l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2526

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2530 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2528l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2529

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2533 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2531l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2532

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2535 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2531r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2534

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2536 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2528r := by
  refine succeed_by_split .spoke 2 7 true (by decide +kernel) ?_ ?_
  · exact h9_2533 hred _
  intro _
  exact h9_2535 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2537 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2525r := by
  refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
  · exact h9_2530 hred _
  intro _
  exact h9_2536 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2538 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2438l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_2527 hred _
  intro _
  exact h9_2537 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2932 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2930l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2931

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2934 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2930r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2933

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2935 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2910l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_2932 hred _
  intro _
  exact h9_2934 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2941 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2939l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2940

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2943 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2939r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2942

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2944 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2937l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact h9_2941 hred _
  intro _
  exact h9_2943 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2949 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2947l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2948

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2951 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2947r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2950

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2952 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2908l := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h9_2949 hred _
  intro _
  exact h9_2951 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2974 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2972l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2973

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2977 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2975l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2976

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2979 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2975r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_2978

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2980 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2972r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact h9_2977 hred _
  intro _
  exact h9_2979 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_2981 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2906l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_2974 hred _
  intro _
  exact h9_2980 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3048 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3046l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3047

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3050 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3046r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3049

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3051 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_2999l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_3048 hred _
  intro _
  exact h9_3050 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3100 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3098l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3099

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3102 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3098r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3101

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3103 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3054l := by
  refine succeed_by_split .spoke 3 7 true (by decide +kernel) ?_ ?_
  · exact h9_3100 hred _
  intro _
  exact h9_3102 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3109 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3107l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3108

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3111 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3107r := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3110

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3112 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3052l := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact h9_3109 hred _
  intro _
  exact h9_3111 hred _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3120 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3118l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3119

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3123 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3121l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3122

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem h9_3126 (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p9_3124l := by
  exact succeed_by_hubcap9 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f9_3125

end FourColor

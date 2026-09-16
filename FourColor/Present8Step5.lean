import FourColor.Present8Step4
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Steps 5 of the arity 8 presentation

A chunk of the case analysis of `present8.v`, in its own module so that its
memory is released before the next. -/

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2789 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_116 p8_2760r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2788
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2787 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8
  intro L2_9
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_9
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 6 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2767 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8 L2_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2794 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_2759 p8_2759l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2793
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2792

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2795 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_116 p8_2758r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact s8_step2794 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2790
  intro _
  exact s8_step2789 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2797 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752)
    (L2_8 : Successful q8_2756) :
    SucceedsIn q8_116 p8_2756r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_8
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2796
  intro _
  exact s8_step2795 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2803 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2756 p8_2799r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2802
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2801

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2819 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2815r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2818
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2817

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2821 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2814r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2820
  intro _
  exact s8_step2819 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2823 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2812r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2822
  intro _
  refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2821 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2825 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2811r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2824
  intro _
  exact s8_step2823 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2827 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2809r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2826
  intro _
  refine succeed_by_split .fan1 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2825 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2829 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2808r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2828
  intro _
  exact s8_step2827 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2831 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2806r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 7 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2830
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2829 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2834 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_2755 p8_2804r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2833
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 1 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2832
  intro _
  exact s8_step2831 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2835 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_116 p8_2754r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2834 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 5 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2803 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7
  intro L2_8
  exact s8_step2797 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7 L2_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2837 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749)
    (L2_7 : Successful q8_2752) :
    SucceedsIn q8_116 p8_2752r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_7
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.two 0 1 5 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2836
  intro _
  exact s8_step2835 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2848 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2752 p8_2844r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2847
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2846

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2856 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2843 p8_2852r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2855
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2854

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2858 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2843 p8_2850r := by
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2857
  intro _
  exact s8_step2856 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2859 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2752 p8_2842r := by
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2858 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 3 1 <|
       Hubcap.one 6 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 7 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2849
  intro _
  exact s8_step2848 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2862 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2752 p8_2840r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 2 4 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2861
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2860
  intro _
  exact s8_step2859 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2871 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2839 p8_2867r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2870
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2869

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2874 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2839 p8_2865r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 2 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 3 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2873
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2872
  intro _
  exact s8_step2871 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2876 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2839 p8_2864r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2875
  intro _
  exact s8_step2874 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2878 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2752 p8_2838r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 4 0 <|
         Hubcap.two 0 6 7 <|
         Hubcap.two 5 7 7 <|
         Hubcap.two 1 2 3 <|
         Hubcap.two 1 3 5 <|
         Hubcap.two 2 3 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2877
    intro _
    exact s8_step2876 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2863
  intro _
  exact s8_step2862 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2889 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2838 p8_2885r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2888
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2887

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2891 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2838 p8_2883r := by
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2890
  intro _
  exact s8_step2889 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2896 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2883 p8_2892r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2895
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2894

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2898 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2838 p8_2882r := by
  refine succeed_by_split .fan1 4 5 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 4 1 <|
         Hubcap.one 7 4 <|
         Hubcap.two 0 1 5 <|
         Hubcap.two 2 3 4 <|
         Hubcap.two 5 6 6 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_2897
    intro _
    exact s8_step2896 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  exact s8_step2891 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2908 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2881 p8_2904r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2907
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2906

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2910 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2881 p8_2902r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2909
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2908 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2912 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2881 p8_2900r := by
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2911
  intro _
  exact s8_step2910 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2913 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2838 p8_2880r := by
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2912 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2899
  intro _
  exact s8_step2898 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2916 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2838 p8_2838l := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 5 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2915
  intro _
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2914
  intro _
  exact s8_step2913 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2933 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2929r := by
  refine succeed_by_split .hat 6 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2932
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2931

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2935 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2928r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2934
  intro _
  exact s8_step2933 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2937 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2927r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2936
  intro _
  exact s8_step2935 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2939 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2926r := by
  refine succeed_by_split .hat 2 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2938
  intro _
  exact s8_step2937 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2941 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2925r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2940
  intro _
  exact s8_step2939 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2943 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2923r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 2 2 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2942
  intro _
  refine succeed_by_split .fan1 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2941 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2945 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2921r := by
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2944
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2943 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2947 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2919r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.two 2 7 5 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2946
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step2945 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2950 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2917r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 7 4 <|
       Hubcap.two 0 6 7 <|
       Hubcap.two 1 2 3 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2949
  intro _
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 2 6 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2948
  intro _
  exact s8_step2947 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2958 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2917 p8_2954r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2957
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2956

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2960 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2917 p8_2953r := by
  refine succeed_by_split .spoke 3 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 1 <|
       Hubcap.one 2 3 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 5 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 3 5 6 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2959
  intro _
  exact s8_step2958 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2961 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_2751 p8_2751l := by
  refine succeed_by_split .spoke 2 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step2960 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  exact s8_step2950 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2962 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747)
    (L2_6 : Successful q8_2749) :
    SucceedsIn q8_116 p8_2749r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact s8_step2961 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
    · exact s8_step2916 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
    intro _
    exact s8_step2878 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6
  intro L2_7
  exact s8_step2837 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6 L2_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2976 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2972r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 2 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2975
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2974

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2982 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2971 p8_2978r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2981
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_2980

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2984 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2971 p8_2971l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2983
  intro _
  exact s8_step2982 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2985 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2970r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s8_step2984 hred L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 3 1 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 4 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2977
  intro _
  exact s8_step2976 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step2988 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2968r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2987
  intro _
  refine succeed_by_split .fan1 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 5 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2986
  intro _
  exact s8_step2985 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3002 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2967 p8_2998r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 5 6 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3001
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3004 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2967 p8_2997r := by
  refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3003
  intro _
  exact s8_step3002 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3006 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2967 p8_2994r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.two 3 5 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3005
  intro _
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3004 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3009 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2967 p8_2992r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 3 4 5 <|
       Hubcap.two 3 5 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3008
  intro _
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3007
  intro _
  exact s8_step3006 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3012 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2967 p8_2990r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3011
  intro _
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 1 6 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3010
  intro _
  exact s8_step3009 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3014 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2966r := by
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
    · exact succeed_by_hubcap8 hred
        (Hubcap.one 6 4 <|
         Hubcap.one 7 4 <|
         Hubcap.two 0 1 4 <|
         Hubcap.two 2 3 3 <|
         Hubcap.two 4 5 5 <|
         Hubcap.nil)
        rfl (by decide +kernel) (by decide +kernel) f8_3013
    intro _
    exact s8_step3012 hred L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_2989
  intro _
  exact s8_step2988 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3025 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2966 p8_3021r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3024
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3023

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3028 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2966 p8_3019r := by
  refine succeed_by_split .hat 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3027
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3026
  intro _
  exact s8_step3025 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3030 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2966 p8_3018r := by
  refine succeed_by_split .hat 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 5 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3029
  intro _
  exact s8_step3028 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3032 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2966 p8_3017r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 4 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3031
  intro _
  exact s8_step3030 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3034 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2966 p8_3015r := by
  refine succeed_by_split .fan1 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3033
  intro _
  exact s8_step3032 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3036 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2964r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3035
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3034 hred L2_1 L2_2 L2_3 L2_4 L2_5
  intro _
  exact s8_step3014 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3039 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745)
    (L2_5 : Successful q8_2747) :
    SucceedsIn q8_2749 p8_2749l := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.two 0 7 7 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3038
  intro _
  refine succeed_by_split .hat 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3037
  intro _
  exact s8_step3036 hred L2_1 L2_2 L2_3 L2_4 L2_5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3060 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3056r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3059
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3058

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3062 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3054r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3061
  intro _
  refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3060 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3064 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3052r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3063
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3062 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3066 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3049r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3065
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3064 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3068 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3048r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3067
  intro _
  exact s8_step3066 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3070 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3047r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 4 <|
       Hubcap.two 3 5 7 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3069
  intro _
  exact s8_step3068 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3084 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3080r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3083
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3082

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3086 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3079r := by
  refine succeed_by_split .hat 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3085
  intro _
  exact s8_step3084 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3088 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3078r := by
  refine succeed_by_split .hat 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 4 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3087
  intro _
  exact s8_step3086 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3090 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3076r := by
  refine succeed_by_split .hat 3 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3089
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3088 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3092 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3073r := by
  refine succeed_by_split .hat 1 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 1 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3091
  intro _
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 0 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3090 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3094 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3072r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3093
  intro _
  exact s8_step3092 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3096 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3071r := by
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3095
  intro _
  exact s8_step3094 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3098 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3047 p8_3047l := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3097
  intro _
  exact s8_step3096 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3100 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3044r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 3 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3099
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3098 hred L2_1 L2_2 L2_3 L2_4
  intro _
  exact s8_step3070 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3102 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3042r := by
  refine succeed_by_split .hat 7 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3101
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3100 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3112 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3042 p8_3108r := by
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3111
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3110

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3114 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3042 p8_3107r := by
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 3 2 <|
       Hubcap.one 4 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 5 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3113
  intro _
  exact s8_step3112 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3117 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3042 p8_3105r := by
  refine succeed_by_split .spoke 2 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 2 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 6 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3116
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 2 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 7 4 <|
       Hubcap.two 3 6 7 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3115
  intro _
  exact s8_step3114 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3119 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_3042 p8_3103r := by
  refine succeed_by_split .spoke 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 6 4 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 1 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3118
  intro _
  refine succeed_by_split .fan1 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3117 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3121 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_3040r := by
  refine succeed_by_split .hat 0 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3120
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 7 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s8_step3119 hred L2_1 L2_2 L2_3 L2_4
  intro _
  exact s8_step3102 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3123 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_2747 p8_2747l := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3122
  intro _
  exact s8_step3121 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3124 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739)
    (L2_4 : Successful q8_2745) :
    SucceedsIn q8_116 p8_2745r := by
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3123 hred L2_1 L2_2 L2_3 L2_4
  intro L2_5
  refine succeed_by_split .spoke 4 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 2 6 false (by decide +kernel) ?_ ?_
  · exact s8_step3039 hred L2_1 L2_2 L2_3 L2_4 L2_5
  intro L2_6
  exact s8_step2962 hred L2_1 L2_2 L2_3 L2_4 L2_5 L2_6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3128 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739) :
    SucceedsIn q8_2745 p8_2745l := by
  refine succeed_by_split .spoke 1 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3127
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3126

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3130 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739) :
    SucceedsIn q8_116 p8_2743r := by
  refine succeed_by_split .spoke 4 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 4 0 <|
       Hubcap.one 5 3 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 2 3 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3129
  intro _
  refine succeed_by_split .spoke 0 7 false (by decide +kernel) ?_ ?_
  · exact s8_step3128 hred L2_1 L2_2 L2_3
  intro L2_4
  exact s8_step3124 hred L2_1 L2_2 L2_3 L2_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3133 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739) :
    SucceedsIn q8_116 p8_2741r := by
  refine succeed_by_split .spoke 2 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 0 <|
       Hubcap.one 3 2 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3132
  intro _
  refine succeed_by_split .spoke 3 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 2 2 <|
       Hubcap.one 3 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 0 1 5 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3131
  intro _
  exact s8_step3130 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3135 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L2_3 : Successful q8_2739) :
    SucceedsIn q8_116 p8_2739r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L2_3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 1 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 0 <|
       Hubcap.one 6 4 <|
       Hubcap.one 7 4 <|
       Hubcap.two 2 3 4 <|
       Hubcap.two 4 5 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3134
  intro _
  exact s8_step3133 hred L2_1 L2_2 L2_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3155 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3151r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3154
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3153

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3157 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3150r := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3156
  intro _
  exact s8_step3155 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3159 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3149r := by
  refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 4 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3158
  intro _
  exact s8_step3157 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3161 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3148r := by
  refine succeed_by_split .spoke 0 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 0 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3160
  intro _
  exact s8_step3159 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3163 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3147r := by
  refine succeed_by_split .spoke 5 8 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 7 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3162
  intro _
  exact s8_step3161 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3166 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3145r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 1 <|
       Hubcap.one 1 3 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3165
  intro _
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 1 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 0 2 4 <|
       Hubcap.two 3 5 4 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3164
  intro _
  exact s8_step3163 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3167 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L3_2 : Successful q8_3141) :
    SucceedsIn q8_2739 p8_3141r := by
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L3_2
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 2 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan1 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3166 hred L2_1 L2_2 L3_1 L3_2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3185 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3181r := by
  refine succeed_by_split .hat 5 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3184
  intro _
  exact succeed_by_hubcap8 hred
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) f8_3183

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3187 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3180r := by
  refine succeed_by_split .hat 3 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 2 1 <|
       Hubcap.one 3 3 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3186
  intro _
  exact s8_step3185 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3189 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3179r := by
  refine succeed_by_split .spoke 5 7 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap8 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 2 <|
       Hubcap.one 4 3 <|
       Hubcap.one 5 1 <|
       Hubcap.one 6 3 <|
       Hubcap.one 7 3 <|
       Hubcap.two 2 3 5 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f8_3188
  intro _
  exact s8_step3187 hred L2_1 L2_2 L3_1 L4_1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem s8_step3190 (hred : RedpartSound theRedpart)
    (L2_1 : Successful q8_2735)
    (L2_2 : Successful q8_2737)
    (L3_1 : Successful q8_3137)
    (L4_1 : Successful q8_3169) :
    SucceedsIn q8_3141 p8_3175r := by
  refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .fan2 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 4 5 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 2 true L4_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  refine succeed_by_split .hat 7 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s8_step3189 hred L2_1 L2_2 L3_1 L4_1

end FourColor

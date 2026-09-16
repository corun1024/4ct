import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 60 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2860l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2860l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2860l) (hubSubn 9 5 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2860l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2865_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2860l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2865 :
    hubcapFit theRedpart rf9 p9_2860l
    (Hubcap.one 0 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 5 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2865_1, c9_2865_2, c9_2865_3, c9_2865_4, c9_2865_5, c9_2865_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2857l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2857l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2857l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2857l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2857l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2857l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2867_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2857l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2867 :
    hubcapFit theRedpart rf9 p9_2857l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2867_1, c9_2867_2, c9_2867_3, c9_2867_4, c9_2867_5, c9_2867_6, c9_2867_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2856l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2856l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2856l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2856l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2856l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2856l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2869_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2856l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2869 :
    hubcapFit theRedpart rf9 p9_2856l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2869_1, c9_2869_2, c9_2869_3, c9_2869_4, c9_2869_5, c9_2869_6, c9_2869_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2855l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2855l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2855l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2871_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2855l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2871 :
    hubcapFit theRedpart rf9 p9_2855l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2871_1, c9_2871_2, c9_2871_3, c9_2871_4, c9_2871_5, c9_2871_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2854l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2854l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2854l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2854l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2854l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2872_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2854l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2872 :
    hubcapFit theRedpart rf9 p9_2854l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2872_1, c9_2872_2, c9_2872_3, c9_2872_4, c9_2872_5, c9_2872_6, c9_2872_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2853l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2853l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2853l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2853l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2853l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2874_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2853l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2874 :
    hubcapFit theRedpart rf9 p9_2853l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2874_1, c9_2874_2, c9_2874_3, c9_2874_4, c9_2874_5, c9_2874_6, c9_2874_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2876_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2842l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2876_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2842l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2876_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2842l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2876_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2842l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2876_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2842l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2876 :
    hubcapFit theRedpart rf9 p9_2842l
    (Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2876_1, c9_2876_2, c9_2876_3, c9_2876_4, c9_2876_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2841l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2841l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2878_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2841l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2878 :
    hubcapFit theRedpart rf9 p9_2841l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2878_1, c9_2878_2, c9_2878_3, c9_2878_4, c9_2878_5, c9_2878_6, c9_2878_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2840l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2840l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2840l) (hubSubn 9 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2840l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2880_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2840l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2880 :
    hubcapFit theRedpart rf9 p9_2840l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2880_1, c9_2880_2, c9_2880_3, c9_2880_4, c9_2880_5, c9_2880_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2839l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2839l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2839l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2881_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2839l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2881 :
    hubcapFit theRedpart rf9 p9_2839l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2881_1, c9_2881_2, c9_2881_3, c9_2881_4, c9_2881_5, c9_2881_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2838l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2838l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2838l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2883_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2838l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2883 :
    hubcapFit theRedpart rf9 p9_2838l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2883_1, c9_2883_2, c9_2883_3, c9_2883_4, c9_2883_5, c9_2883_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2884_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2837l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2884_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2837l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2884_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2837l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2884_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2837l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2884_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2837l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2884 :
    hubcapFit theRedpart rf9 p9_2837l
    (Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2884_1, c9_2884_2, c9_2884_3, c9_2884_4, c9_2884_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2731l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2731l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2731l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2731l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2731l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2731l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2886_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2731l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2886 :
    hubcapFit theRedpart rf9 p9_2731l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2886_1, c9_2886_2, c9_2886_3, c9_2886_4, c9_2886_5, c9_2886_6, c9_2886_7, c9_2886_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2730l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2730l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2730l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2730l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2730l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2730l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2888_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2730l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2888 :
    hubcapFit theRedpart rf9 p9_2730l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2888_1, c9_2888_2, c9_2888_3, c9_2888_4, c9_2888_5, c9_2888_6, c9_2888_7, c9_2888_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2729l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2729l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2729l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2729l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2729l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2729l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2729l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2890_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2729l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2890 :
    hubcapFit theRedpart rf9 p9_2729l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2890_1, c9_2890_2, c9_2890_3, c9_2890_4, c9_2890_5, c9_2890_6, c9_2890_7, c9_2890_8, c9_2890_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2728l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2728l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2728l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2728l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2728l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2728l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2892_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2728l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2892 :
    hubcapFit theRedpart rf9 p9_2728l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2892_1, c9_2892_2, c9_2892_3, c9_2892_4, c9_2892_5, c9_2892_6, c9_2892_7, c9_2892_8, c9_2892_9]

end FourColor

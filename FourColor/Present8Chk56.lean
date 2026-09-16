import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 56 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2852l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2852l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2852l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2857_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2852l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2857 :
    hubcapFit theRedpart rf8 p8_2852l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2857_1, c8_2857_2, c8_2857_3, c8_2857_4, c8_2857_5, c8_2857_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2842l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2860_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2842l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2860 :
    hubcapFit theRedpart rf8 p8_2842l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2860_1, c8_2860_2, c8_2860_3, c8_2860_4, c8_2860_5, c8_2860_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2841l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2841l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2841l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2841l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2861_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2841l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2861 :
    hubcapFit theRedpart rf8 p8_2841l
    (Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2861_1, c8_2861_2, c8_2861_3, c8_2861_4, c8_2861_5, c8_2861_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2840l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2840l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2840l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2840l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2863_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2840l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2863 :
    hubcapFit theRedpart rf8 p8_2840l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2863_1, c8_2863_2, c8_2863_3, c8_2863_4, c8_2863_5, c8_2863_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2869_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2868r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2869_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2868r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2869_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2868r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2869_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2868r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2869_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2868r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2869 :
    hubcapFit theRedpart rf8 p8_2868r
    (Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2869_1, c8_2869_2, c8_2869_3, c8_2869_4, c8_2869_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2868l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2868l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2868l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2868l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2868l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2870_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2868l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2870 :
    hubcapFit theRedpart rf8 p8_2868l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2870_1, c8_2870_2, c8_2870_3, c8_2870_4, c8_2870_5, c8_2870_6, c8_2870_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2872_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2867l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2872_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2867l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2872_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2867l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2872_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2867l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2872_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2867l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2872 :
    hubcapFit theRedpart rf8 p8_2867l
    (Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2872_1, c8_2872_2, c8_2872_3, c8_2872_4, c8_2872_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2866l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2866l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2866l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2866l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2866l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2873_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2866l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2873 :
    hubcapFit theRedpart rf8 p8_2866l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2873_1, c8_2873_2, c8_2873_3, c8_2873_4, c8_2873_5, c8_2873_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2865l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2865l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2865l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2875_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2865l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2875 :
    hubcapFit theRedpart rf8 p8_2865l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2875_1, c8_2875_2, c8_2875_3, c8_2875_4, c8_2875_5, c8_2875_6, c8_2875_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2864l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2864l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2864l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2864l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2864l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2877_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2864l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2877 :
    hubcapFit theRedpart rf8 p8_2864l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 5 7 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2877_1, c8_2877_2, c8_2877_3, c8_2877_4, c8_2877_5, c8_2877_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2887_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2886r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2887_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2886r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2887_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2886r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2887_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2886r) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2887_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2886r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2887 :
    hubcapFit theRedpart rf8 p8_2886r
    (Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2887_1, c8_2887_2, c8_2887_3, c8_2887_4, c8_2887_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2886l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2886l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2886l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2886l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2888_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2886l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2888 :
    hubcapFit theRedpart rf8 p8_2886l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2888_1, c8_2888_2, c8_2888_3, c8_2888_4, c8_2888_5, c8_2888_6, c8_2888_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2885l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2885l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2885l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2885l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2885l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2890_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2885l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2890 :
    hubcapFit theRedpart rf8 p8_2885l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2890_1, c8_2890_2, c8_2890_3, c8_2890_4, c8_2890_5, c8_2890_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2894_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2893r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2894_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2893r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2894_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2893r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2894_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2893r) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2894_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2893r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2894 :
    hubcapFit theRedpart rf8 p8_2893r
    (Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2894_1, c8_2894_2, c8_2894_3, c8_2894_4, c8_2894_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2893l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2893l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2893l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2893l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2895_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2893l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2895 :
    hubcapFit theRedpart rf8 p8_2893l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2895_1, c8_2895_2, c8_2895_3, c8_2895_4, c8_2895_5, c8_2895_6, c8_2895_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2897_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2892l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2897_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2892l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2897_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2892l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2897_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2892l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2897_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2892l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2897 :
    hubcapFit theRedpart rf8 p8_2892l
    (Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2897_1, c8_2897_2, c8_2897_3, c8_2897_4, c8_2897_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2882l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2882l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2882l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2882l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2882l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2899_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2882l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2899 :
    hubcapFit theRedpart rf8 p8_2882l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2899_1, c8_2899_2, c8_2899_3, c8_2899_4, c8_2899_5, c8_2899_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2905r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2905r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2905r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2905r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2905r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2906_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2905r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2906 :
    hubcapFit theRedpart rf8 p8_2905r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2906_1, c8_2906_2, c8_2906_3, c8_2906_4, c8_2906_5, c8_2906_6]

end FourColor

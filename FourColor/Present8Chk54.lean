import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 54 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2695l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2724_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2724 :
    hubcapFit theRedpart rf8 p8_2695l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2724_1, c8_2724_2, c8_2724_3, c8_2724_4, c8_2724_5, c8_2724_6, c8_2724_7, c8_2724_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2694l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2694l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2694l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2726_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2694l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2726 :
    hubcapFit theRedpart rf8 p8_2694l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2726_1, c8_2726_2, c8_2726_3, c8_2726_4, c8_2726_5, c8_2726_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2659l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2659l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2659l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2659l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2728_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2659l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2728 :
    hubcapFit theRedpart rf8 p8_2659l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 5 7 6 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2728_1, c8_2728_2, c8_2728_3, c8_2728_4, c8_2728_5, c8_2728_6, c8_2728_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2608l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2608l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2608l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2608l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2730_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2608l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2730 :
    hubcapFit theRedpart rf8 p8_2608l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2730_1, c8_2730_2, c8_2730_3, c8_2730_4, c8_2730_5, c8_2730_6, c8_2730_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2765r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2765r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2765r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2765r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2766_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2765r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2766 :
    hubcapFit theRedpart rf8 p8_2765r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2766_1, c8_2766_2, c8_2766_3, c8_2766_4, c8_2766_5, c8_2766_6, c8_2766_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2775r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2775r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2775r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2775r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2775r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2775r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2776_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2775r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2776 :
    hubcapFit theRedpart rf8 p8_2775r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2776_1, c8_2776_2, c8_2776_3, c8_2776_4, c8_2776_5, c8_2776_6, c8_2776_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2775l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2775l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2775l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2777_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2777 :
    hubcapFit theRedpart rf8 p8_2775l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2777_1, c8_2777_2, c8_2777_3, c8_2777_4, c8_2777_5, c8_2777_6, c8_2777_7, c8_2777_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2774l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2774l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2774l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2779_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2774l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2779 :
    hubcapFit theRedpart rf8 p8_2774l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2779_1, c8_2779_2, c8_2779_3, c8_2779_4, c8_2779_5, c8_2779_6, c8_2779_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2772l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2772l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2772l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2781_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2772l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2781 :
    hubcapFit theRedpart rf8 p8_2772l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2781_1, c8_2781_2, c8_2781_3, c8_2781_4, c8_2781_5, c8_2781_6, c8_2781_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2783_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2783_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2783_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2770l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2783_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2770l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2783_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2770l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2783 :
    hubcapFit theRedpart rf8 p8_2770l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2783_1, c8_2783_2, c8_2783_3, c8_2783_4, c8_2783_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2785_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2785_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2769l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2785_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2769l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2785_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2769l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2785_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2769l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2785 :
    hubcapFit theRedpart rf8 p8_2769l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2785_1, c8_2785_2, c8_2785_3, c8_2785_4, c8_2785_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2768l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2768l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2768l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2768l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2786_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2768l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2786 :
    hubcapFit theRedpart rf8 p8_2768l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2786_1, c8_2786_2, c8_2786_3, c8_2786_4, c8_2786_5, c8_2786_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2788_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2761l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2788_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2761l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2788_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2761l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2788_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2761l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2788_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2761l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2788 :
    hubcapFit theRedpart rf8 p8_2761l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2788_1, c8_2788_2, c8_2788_3, c8_2788_4, c8_2788_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2790_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2760l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2790_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2760l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2790_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2760l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2790_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2760l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2790_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2760l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2790 :
    hubcapFit theRedpart rf8 p8_2760l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2790_1, c8_2790_2, c8_2790_3, c8_2790_4, c8_2790_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2792_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2791r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2792_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2791r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2792_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2791r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2792_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2791r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2792_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2791r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2792 :
    hubcapFit theRedpart rf8 p8_2791r
    (Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2792_1, c8_2792_2, c8_2792_3, c8_2792_4, c8_2792_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2793_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2791l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2793_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2791l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2793_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2791l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2793_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2791l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2793_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2791l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2793 :
    hubcapFit theRedpart rf8 p8_2791l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2793_1, c8_2793_2, c8_2793_3, c8_2793_4, c8_2793_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2758l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2758l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2758l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2758l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2758l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2796_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2758l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2796 :
    hubcapFit theRedpart rf8 p8_2758l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2796_1, c8_2796_2, c8_2796_3, c8_2796_4, c8_2796_5, c8_2796_6]

end FourColor

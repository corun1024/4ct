import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 48 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2649r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2649r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2649r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2649r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2649r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2650_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2649r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2650 :
    hubcapFit theRedpart rf7 p7_2649r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2650_1, c7_2650_2, c7_2650_3, c7_2650_4, c7_2650_5, c7_2650_6, c7_2650_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2649l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2649l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2649l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2651_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2651 :
    hubcapFit theRedpart rf7 p7_2649l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2651_1, c7_2651_2, c7_2651_3, c7_2651_4, c7_2651_5, c7_2651_6, c7_2651_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2648l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2648l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2648l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2648l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2648l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2653_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2648l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2653 :
    hubcapFit theRedpart rf7 p7_2648l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2653_1, c7_2653_2, c7_2653_3, c7_2653_4, c7_2653_5, c7_2653_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2647l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2647l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2647l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2647l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2654_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2654 :
    hubcapFit theRedpart rf7 p7_2647l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2654_1, c7_2654_2, c7_2654_3, c7_2654_4, c7_2654_5, c7_2654_6, c7_2654_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2645l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2645l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2645l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2645l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2645l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2645l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2656_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2645l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2656 :
    hubcapFit theRedpart rf7 p7_2645l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2656_1, c7_2656_2, c7_2656_3, c7_2656_4, c7_2656_5, c7_2656_6, c7_2656_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2644l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2644l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2658_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2644l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2658 :
    hubcapFit theRedpart rf7 p7_2644l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2658_1, c7_2658_2, c7_2658_3, c7_2658_4, c7_2658_5, c7_2658_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2659_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2643l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2659_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2643l) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2659_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2643l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2659_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2643l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2659 :
    hubcapFit theRedpart rf7 p7_2643l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2659_1, c7_2659_2, c7_2659_3, c7_2659_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2661_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2642l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2661_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2642l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2661_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2642l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2661_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2642l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2661_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2642l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2661 :
    hubcapFit theRedpart rf7 p7_2642l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2661_1, c7_2661_2, c7_2661_3, c7_2661_4, c7_2661_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2664_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2663r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2664_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2663r) (hubSubn 7 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2664_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2663r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2664_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2663r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2664 :
    hubcapFit theRedpart rf7 p7_2663r
    (Hubcap.one 6 1 <|
     Hubcap.two 0 5 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2664_1, c7_2664_2, c7_2664_3, c7_2664_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2665_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2665_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2663l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2665_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2665_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2663l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2665_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2663l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2665 :
    hubcapFit theRedpart rf7 p7_2663l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2665_1, c7_2665_2, c7_2665_3, c7_2665_4, c7_2665_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2669r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2669r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2669r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2669r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2670_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2669r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2670 :
    hubcapFit theRedpart rf7 p7_2669r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2670_1, c7_2670_2, c7_2670_3, c7_2670_4, c7_2670_5, c7_2670_6, c7_2670_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2671_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2671_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2669l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2671_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2669l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2671_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2669l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2671_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2669l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2671 :
    hubcapFit theRedpart rf7 p7_2669l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2671_1, c7_2671_2, c7_2671_3, c7_2671_4, c7_2671_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2668l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2668l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2668l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2673_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2668l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2673 :
    hubcapFit theRedpart rf7 p7_2668l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2673_1, c7_2673_2, c7_2673_3, c7_2673_4, c7_2673_5, c7_2673_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2674_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2674_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2667l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2674_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2667l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2674_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2667l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2674_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2667l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2674 :
    hubcapFit theRedpart rf7 p7_2667l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2674_1, c7_2674_2, c7_2674_3, c7_2674_4, c7_2674_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2680_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2679r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2680_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2679r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2680_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2679r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2680_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2679r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2680_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2679r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2680 :
    hubcapFit theRedpart rf7 p7_2679r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2680_1, c7_2680_2, c7_2680_3, c7_2680_4, c7_2680_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2679l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2679l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2679l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2681_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2679l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2681 :
    hubcapFit theRedpart rf7 p7_2679l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2681_1, c7_2681_2, c7_2681_3, c7_2681_4, c7_2681_5, c7_2681_6, c7_2681_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2678l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2678l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2678l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2683_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2678l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2683 :
    hubcapFit theRedpart rf7 p7_2678l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2683_1, c7_2683_2, c7_2683_3, c7_2683_4, c7_2683_5, c7_2683_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2684_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2684_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2677l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2684_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2677l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2684_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2677l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2684 :
    hubcapFit theRedpart rf7 p7_2677l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2684_1, c7_2684_2, c7_2684_3, c7_2684_4]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 52 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2618l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2632_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2618l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2632 :
    hubcapFit theRedpart rf8 p8_2618l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2632_1, c8_2632_2, c8_2632_3, c8_2632_4, c8_2632_5, c8_2632_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2617l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2617l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2617l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2634_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2617l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2634 :
    hubcapFit theRedpart rf8 p8_2617l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2634_1, c8_2634_2, c8_2634_3, c8_2634_4, c8_2634_5, c8_2634_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2635_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2635_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2635_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2616l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2635_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2616l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2635_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2616l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2635 :
    hubcapFit theRedpart rf8 p8_2616l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2635_1, c8_2635_2, c8_2635_3, c8_2635_4, c8_2635_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2637_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2615l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2637_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2637_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2615l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2637_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2615l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2637_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2615l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2637 :
    hubcapFit theRedpart rf8 p8_2615l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2637_1, c8_2637_2, c8_2637_3, c8_2637_4, c8_2637_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2614l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2614l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2614l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2638_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2614l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2638 :
    hubcapFit theRedpart rf8 p8_2614l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2638_1, c8_2638_2, c8_2638_3, c8_2638_4, c8_2638_5, c8_2638_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2613l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2613l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2613l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2640_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2613l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2640 :
    hubcapFit theRedpart rf8 p8_2613l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2640_1, c8_2640_2, c8_2640_3, c8_2640_4, c8_2640_5, c8_2640_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2646r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2646r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2646r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2646r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2646r) (hubSubn 8 5 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2647_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2646r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2647 :
    hubcapFit theRedpart rf8 p8_2646r
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 5 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2647_1, c8_2647_2, c8_2647_3, c8_2647_4, c8_2647_5, c8_2647_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2648_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2648_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2648_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2646l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2648_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2646l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2648_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2646l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2648 :
    hubcapFit theRedpart rf8 p8_2646l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2648_1, c8_2648_2, c8_2648_3, c8_2648_4, c8_2648_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2650_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2650_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2650_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2644l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2650_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2644l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2650_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2644l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2650 :
    hubcapFit theRedpart rf8 p8_2644l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2650_1, c8_2650_2, c8_2650_3, c8_2650_4, c8_2650_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2652_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2643l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2652_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2643l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2652_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2643l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2652_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2643l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2652_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2643l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2652 :
    hubcapFit theRedpart rf8 p8_2643l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2652_1, c8_2652_2, c8_2652_3, c8_2652_4, c8_2652_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2653_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2653_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2653_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2642l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2653_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2642l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2653_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2642l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2653 :
    hubcapFit theRedpart rf8 p8_2642l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2653_1, c8_2653_2, c8_2653_3, c8_2653_4, c8_2653_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2641l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2655_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2641l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2655 :
    hubcapFit theRedpart rf8 p8_2641l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2655_1, c8_2655_2, c8_2655_3, c8_2655_4, c8_2655_5, c8_2655_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2611l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2611l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2611l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2611l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2611l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2657_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2611l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2657 :
    hubcapFit theRedpart rf8 p8_2611l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2657_1, c8_2657_2, c8_2657_3, c8_2657_4, c8_2657_5, c8_2657_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2672r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2672r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2672r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2672r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2672r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2672r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2672r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2673_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2672r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2673 :
    hubcapFit theRedpart rf8 p8_2672r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2673_1, c8_2673_2, c8_2673_3, c8_2673_4, c8_2673_5, c8_2673_6, c8_2673_7, c8_2673_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2672l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2672l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2672l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2672l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2672l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2672l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2674_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2672l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2674 :
    hubcapFit theRedpart rf8 p8_2672l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2674_1, c8_2674_2, c8_2674_3, c8_2674_4, c8_2674_5, c8_2674_6, c8_2674_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2671l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2671l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2676_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2676 :
    hubcapFit theRedpart rf8 p8_2671l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2676_1, c8_2676_2, c8_2676_3, c8_2676_4, c8_2676_5, c8_2676_6, c8_2676_7, c8_2676_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2670l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2670l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2678_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2670l) (hubSubn 8 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2678 :
    hubcapFit theRedpart rf8 p8_2670l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2678_1, c8_2678_2, c8_2678_3, c8_2678_4, c8_2678_5, c8_2678_6, c8_2678_7]

end FourColor

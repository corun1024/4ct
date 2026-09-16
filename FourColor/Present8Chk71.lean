import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 71 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3601l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3601l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3601l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3603_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3601l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3603 :
    hubcapFit theRedpart rf8 p8_3601l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3603_1, c8_3603_2, c8_3603_3, c8_3603_4, c8_3603_5, c8_3603_6, c8_3603_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3599l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3599l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3599l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3599l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3605_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3599l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3605 :
    hubcapFit theRedpart rf8 p8_3599l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3605_1, c8_3605_2, c8_3605_3, c8_3605_4, c8_3605_5, c8_3605_6, c8_3605_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3597l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3597l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3597l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3597l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3607_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3597l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3607 :
    hubcapFit theRedpart rf8 p8_3597l
    (Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3607_1, c8_3607_2, c8_3607_3, c8_3607_4, c8_3607_5, c8_3607_6, c8_3607_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3609r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3609r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3609r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3609r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3609r) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3610_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3609r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3610 :
    hubcapFit theRedpart rf8 p8_3609r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3610_1, c8_3610_2, c8_3610_3, c8_3610_4, c8_3610_5, c8_3610_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3609l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3611_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3609l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3611 :
    hubcapFit theRedpart rf8 p8_3609l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3611_1, c8_3611_2, c8_3611_3, c8_3611_4, c8_3611_5, c8_3611_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3594l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3613_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3594l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3613 :
    hubcapFit theRedpart rf8 p8_3594l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3613_1, c8_3613_2, c8_3613_3, c8_3613_4, c8_3613_5, c8_3613_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3593l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3615_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3593l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3615 :
    hubcapFit theRedpart rf8 p8_3593l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3615_1, c8_3615_2, c8_3615_3, c8_3615_4, c8_3615_5, c8_3615_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3592l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3592l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3616_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3592l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3616 :
    hubcapFit theRedpart rf8 p8_3592l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3616_1, c8_3616_2, c8_3616_3, c8_3616_4, c8_3616_5, c8_3616_6, c8_3616_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3591l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3591l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3591l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3618_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3591l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3618 :
    hubcapFit theRedpart rf8 p8_3591l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3618_1, c8_3618_2, c8_3618_3, c8_3618_4, c8_3618_5, c8_3618_6, c8_3618_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3508l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3508l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3508l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3620_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3508l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3620 :
    hubcapFit theRedpart rf8 p8_3508l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3620_1, c8_3620_2, c8_3620_3, c8_3620_4, c8_3620_5, c8_3620_6, c8_3620_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3507l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3507l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3507l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3622_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3507l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3622 :
    hubcapFit theRedpart rf8 p8_3507l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3622_1, c8_3622_2, c8_3622_3, c8_3622_4, c8_3622_5, c8_3622_6, c8_3622_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3646r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3646r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3646r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3646r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3646r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3646r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3647_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3646r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3647 :
    hubcapFit theRedpart rf8 p8_3646r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3647_1, c8_3647_2, c8_3647_3, c8_3647_4, c8_3647_5, c8_3647_6, c8_3647_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3646l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3646l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3646l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3646l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3648_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3646l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3648 :
    hubcapFit theRedpart rf8 p8_3646l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3648_1, c8_3648_2, c8_3648_3, c8_3648_4, c8_3648_5, c8_3648_6, c8_3648_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3644l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3644l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3644l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3650_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3644l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3650 :
    hubcapFit theRedpart rf8 p8_3644l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3650_1, c8_3650_2, c8_3650_3, c8_3650_4, c8_3650_5, c8_3650_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3643l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3643l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3643l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3643l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3643l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3643l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3652_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3643l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3652 :
    hubcapFit theRedpart rf8 p8_3643l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3652_1, c8_3652_2, c8_3652_3, c8_3652_4, c8_3652_5, c8_3652_6, c8_3652_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3642l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3642l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3642l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3642l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3642l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3642l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3654_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3642l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3654 :
    hubcapFit theRedpart rf8 p8_3642l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3654_1, c8_3654_2, c8_3654_3, c8_3654_4, c8_3654_5, c8_3654_6, c8_3654_7, c8_3654_8]

end FourColor

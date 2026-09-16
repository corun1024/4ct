import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 80 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4007l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4007l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4007l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4007l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4018_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4007l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4018 :
    hubcapFit theRedpart rf8 p8_4007l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4018_1, c8_4018_2, c8_4018_3, c8_4018_4, c8_4018_5, c8_4018_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4006l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4006l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4006l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4019_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4006l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4019 :
    hubcapFit theRedpart rf8 p8_4006l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4019_1, c8_4019_2, c8_4019_3, c8_4019_4, c8_4019_5, c8_4019_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4004l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4004l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4004l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4004l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4004l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4021_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4004l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4021 :
    hubcapFit theRedpart rf8 p8_4004l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4021_1, c8_4021_2, c8_4021_3, c8_4021_4, c8_4021_5, c8_4021_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4003l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4003l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4003l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4003l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4023_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4003l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4023 :
    hubcapFit theRedpart rf8 p8_4003l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4023_1, c8_4023_2, c8_4023_3, c8_4023_4, c8_4023_5, c8_4023_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4038r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4038r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4038r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4038r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4038r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4038r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4039_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4038r) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4039 :
    hubcapFit theRedpart rf8 p8_4038r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4039_1, c8_4039_2, c8_4039_3, c8_4039_4, c8_4039_5, c8_4039_6, c8_4039_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4038l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4038l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4038l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4038l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4038l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4038l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4040_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4038l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4040 :
    hubcapFit theRedpart rf8 p8_4038l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4040_1, c8_4040_2, c8_4040_3, c8_4040_4, c8_4040_5, c8_4040_6, c8_4040_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4036l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4036l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4042_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4036l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4042 :
    hubcapFit theRedpart rf8 p8_4036l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4042_1, c8_4042_2, c8_4042_3, c8_4042_4, c8_4042_5, c8_4042_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4034l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4034l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4034l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4034l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4034l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4044_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4034l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4044 :
    hubcapFit theRedpart rf8 p8_4034l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4044_1, c8_4044_2, c8_4044_3, c8_4044_4, c8_4044_5, c8_4044_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4054r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4054r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4054r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4054r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4054r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4054r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4054r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4055_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4054r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4055 :
    hubcapFit theRedpart rf8 p8_4054r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4055_1, c8_4055_2, c8_4055_3, c8_4055_4, c8_4055_5, c8_4055_6, c8_4055_7, c8_4055_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4054l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4054l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4056_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4054l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4056 :
    hubcapFit theRedpart rf8 p8_4054l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4056_1, c8_4056_2, c8_4056_3, c8_4056_4, c8_4056_5, c8_4056_6, c8_4056_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4053l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4053l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4058_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4053l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4058 :
    hubcapFit theRedpart rf8 p8_4053l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4058_1, c8_4058_2, c8_4058_3, c8_4058_4, c8_4058_5, c8_4058_6, c8_4058_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4052l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4052l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4060_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4052l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4060 :
    hubcapFit theRedpart rf8 p8_4052l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4060_1, c8_4060_2, c8_4060_3, c8_4060_4, c8_4060_5, c8_4060_6, c8_4060_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4051l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4051l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4051l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4062_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4051l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4062 :
    hubcapFit theRedpart rf8 p8_4051l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4062_1, c8_4062_2, c8_4062_3, c8_4062_4, c8_4062_5, c8_4062_6, c8_4062_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4050l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4050l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4064_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4050l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4064 :
    hubcapFit theRedpart rf8 p8_4050l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4064_1, c8_4064_2, c8_4064_3, c8_4064_4, c8_4064_5, c8_4064_6, c8_4064_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4049l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4049l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4049l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4049l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4066_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4049l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4066 :
    hubcapFit theRedpart rf8 p8_4049l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4066_1, c8_4066_2, c8_4066_3, c8_4066_4, c8_4066_5, c8_4066_6, c8_4066_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4048l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4048l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4068_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4068 :
    hubcapFit theRedpart rf8 p8_4048l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4068_1, c8_4068_2, c8_4068_3, c8_4068_4, c8_4068_5, c8_4068_6, c8_4068_7, c8_4068_8]

end FourColor

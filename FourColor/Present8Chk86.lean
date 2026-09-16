import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 86 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4304_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4304_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4304_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4279l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4304_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4279l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4304_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4279l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4304 :
    hubcapFit theRedpart rf8 p8_4279l
    (Hubcap.one 0 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4304_1, c8_4304_2, c8_4304_3, c8_4304_4, c8_4304_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4318r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4318r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4318r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4318r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4318r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4318r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4318r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4319_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4318r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4319 :
    hubcapFit theRedpart rf8 p8_4318r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4319_1, c8_4319_2, c8_4319_3, c8_4319_4, c8_4319_5, c8_4319_6, c8_4319_7, c8_4319_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4318l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4318l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4318l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4318l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4318l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4320_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4318l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4320 :
    hubcapFit theRedpart rf8 p8_4318l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4320_1, c8_4320_2, c8_4320_3, c8_4320_4, c8_4320_5, c8_4320_6, c8_4320_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4317l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4317l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4322_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4317l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4322 :
    hubcapFit theRedpart rf8 p8_4317l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4322_1, c8_4322_2, c8_4322_3, c8_4322_4, c8_4322_5, c8_4322_6, c8_4322_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4324_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4315l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4324 :
    hubcapFit theRedpart rf8 p8_4315l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4324_1, c8_4324_2, c8_4324_3, c8_4324_4, c8_4324_5, c8_4324_6, c8_4324_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4313l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4313l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4313l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4313l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4313l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4326_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4313l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4326 :
    hubcapFit theRedpart rf8 p8_4313l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4326_1, c8_4326_2, c8_4326_3, c8_4326_4, c8_4326_5, c8_4326_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4312l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4312l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4312l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4328_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4312l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4328 :
    hubcapFit theRedpart rf8 p8_4312l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4328_1, c8_4328_2, c8_4328_3, c8_4328_4, c8_4328_5, c8_4328_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4311l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4311l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4311l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4311l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4311l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4311l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4329_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4311l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4329 :
    hubcapFit theRedpart rf8 p8_4311l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4329_1, c8_4329_2, c8_4329_3, c8_4329_4, c8_4329_5, c8_4329_6, c8_4329_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4340r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4340r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4340r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4340r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4340r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4340r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4340r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4341_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4340r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4341 :
    hubcapFit theRedpart rf8 p8_4340r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4341_1, c8_4341_2, c8_4341_3, c8_4341_4, c8_4341_5, c8_4341_6, c8_4341_7, c8_4341_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4340l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4340l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4340l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4340l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4342_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4342 :
    hubcapFit theRedpart rf8 p8_4340l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4342_1, c8_4342_2, c8_4342_3, c8_4342_4, c8_4342_5, c8_4342_6, c8_4342_7, c8_4342_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4344_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4344 :
    hubcapFit theRedpart rf8 p8_4339l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4344_1, c8_4344_2, c8_4344_3, c8_4344_4, c8_4344_5, c8_4344_6, c8_4344_7, c8_4344_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4338l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4338l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4338l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4338l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4338l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4346_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4338l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4346 :
    hubcapFit theRedpart rf8 p8_4338l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4346_1, c8_4346_2, c8_4346_3, c8_4346_4, c8_4346_5, c8_4346_6, c8_4346_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4337l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4337l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4337l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4337l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4337l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4348_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4337l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4348 :
    hubcapFit theRedpart rf8 p8_4337l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4348_1, c8_4348_2, c8_4348_3, c8_4348_4, c8_4348_5, c8_4348_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4336l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4336l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4349_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4336l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4349 :
    hubcapFit theRedpart rf8 p8_4336l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4349_1, c8_4349_2, c8_4349_3, c8_4349_4, c8_4349_5, c8_4349_6, c8_4349_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4335l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4351_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4351 :
    hubcapFit theRedpart rf8 p8_4335l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4351_1, c8_4351_2, c8_4351_3, c8_4351_4, c8_4351_5, c8_4351_6, c8_4351_7, c8_4351_8]

end FourColor

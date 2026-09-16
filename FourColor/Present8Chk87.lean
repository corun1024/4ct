import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 87 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4333l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4353_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4333l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4353 :
    hubcapFit theRedpart rf8 p8_4333l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4353_1, c8_4353_2, c8_4353_3, c8_4353_4, c8_4353_5, c8_4353_6, c8_4353_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4332l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4332l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4355_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4355 :
    hubcapFit theRedpart rf8 p8_4332l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4355_1, c8_4355_2, c8_4355_3, c8_4355_4, c8_4355_5, c8_4355_6, c8_4355_7, c8_4355_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4331l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4357_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4331l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4357 :
    hubcapFit theRedpart rf8 p8_4331l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4357_1, c8_4357_2, c8_4357_3, c8_4357_4, c8_4357_5, c8_4357_6, c8_4357_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4359_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4308l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4359_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4359_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4308l) (hubSubn 8 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4359_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4308l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4359_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4308l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4359 :
    hubcapFit theRedpart rf8 p8_4308l
    (Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4359_1, c8_4359_2, c8_4359_3, c8_4359_4, c8_4359_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4307l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4307l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4361_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4307l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4361 :
    hubcapFit theRedpart rf8 p8_4307l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4361_1, c8_4361_2, c8_4361_3, c8_4361_4, c8_4361_5, c8_4361_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4226l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4226l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4226l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4226l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4363_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4226l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4363 :
    hubcapFit theRedpart rf8 p8_4226l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4363_1, c8_4363_2, c8_4363_3, c8_4363_4, c8_4363_5, c8_4363_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4376r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4376r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4376r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4376r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4376r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4376r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4377_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4376r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4377 :
    hubcapFit theRedpart rf8 p8_4376r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4377_1, c8_4377_2, c8_4377_3, c8_4377_4, c8_4377_5, c8_4377_6, c8_4377_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4376l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4376l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4376l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4378_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4376l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4378 :
    hubcapFit theRedpart rf8 p8_4376l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4378_1, c8_4378_2, c8_4378_3, c8_4378_4, c8_4378_5, c8_4378_6, c8_4378_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4380_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4374l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4380 :
    hubcapFit theRedpart rf8 p8_4374l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4380_1, c8_4380_2, c8_4380_3, c8_4380_4, c8_4380_5, c8_4380_6, c8_4380_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4373l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4382_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4373l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4382 :
    hubcapFit theRedpart rf8 p8_4373l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4382_1, c8_4382_2, c8_4382_3, c8_4382_4, c8_4382_5, c8_4382_6, c8_4382_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4372l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4372l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4372l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4372l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4384_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4384 :
    hubcapFit theRedpart rf8 p8_4372l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4384_1, c8_4384_2, c8_4384_3, c8_4384_4, c8_4384_5, c8_4384_6, c8_4384_7, c8_4384_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4371l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4371l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4386_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4371l) (hubSubn 8 4 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4386 :
    hubcapFit theRedpart rf8 p8_4371l
    (Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4386_1, c8_4386_2, c8_4386_3, c8_4386_4, c8_4386_5, c8_4386_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4393r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4393r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4393r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4393r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4394_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4393r) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4394 :
    hubcapFit theRedpart rf8 p8_4393r
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4394_1, c8_4394_2, c8_4394_3, c8_4394_4, c8_4394_5, c8_4394_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4393l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4395_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4393l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4395 :
    hubcapFit theRedpart rf8 p8_4393l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4395_1, c8_4395_2, c8_4395_3, c8_4395_4, c8_4395_5, c8_4395_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4392l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4392l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4397_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4392l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4397 :
    hubcapFit theRedpart rf8 p8_4392l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4397_1, c8_4397_2, c8_4397_3, c8_4397_4, c8_4397_5, c8_4397_6, c8_4397_7, c8_4397_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4391l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4391l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4391l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4391l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4399_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4391l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4399 :
    hubcapFit theRedpart rf8 p8_4391l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4399_1, c8_4399_2, c8_4399_3, c8_4399_4, c8_4399_5, c8_4399_6, c8_4399_7, c8_4399_8]

end FourColor

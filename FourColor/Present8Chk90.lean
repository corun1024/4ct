import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 90 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4490l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4498_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4490l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4498 :
    hubcapFit theRedpart rf8 p8_4490l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4498_1, c8_4498_2, c8_4498_3, c8_4498_4, c8_4498_5, c8_4498_6, c8_4498_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4489l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4489l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4500_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4489l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4500 :
    hubcapFit theRedpart rf8 p8_4489l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4500_1, c8_4500_2, c8_4500_3, c8_4500_4, c8_4500_5, c8_4500_6, c8_4500_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4487l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4487l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4487l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4502_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4487l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4502 :
    hubcapFit theRedpart rf8 p8_4487l
    (Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4502_1, c8_4502_2, c8_4502_3, c8_4502_4, c8_4502_5, c8_4502_6, c8_4502_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4486l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4486l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4486l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4504_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4486l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4504 :
    hubcapFit theRedpart rf8 p8_4486l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4504_1, c8_4504_2, c8_4504_3, c8_4504_4, c8_4504_5, c8_4504_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4458l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4458l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4458l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4458l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4506_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4458l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4506 :
    hubcapFit theRedpart rf8 p8_4458l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4506_1, c8_4506_2, c8_4506_3, c8_4506_4, c8_4506_5, c8_4506_6, c8_4506_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4457l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4457l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4457l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4457l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4508_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4457l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4508 :
    hubcapFit theRedpart rf8 p8_4457l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4508_1, c8_4508_2, c8_4508_3, c8_4508_4, c8_4508_5, c8_4508_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4456l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4509_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4456l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4509 :
    hubcapFit theRedpart rf8 p8_4456l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4509_1, c8_4509_2, c8_4509_3, c8_4509_4, c8_4509_5, c8_4509_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4526r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4526r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4527_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4526r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4527 :
    hubcapFit theRedpart rf8 p8_4526r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4527_1, c8_4527_2, c8_4527_3, c8_4527_4, c8_4527_5, c8_4527_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4526l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4528_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4528 :
    hubcapFit theRedpart rf8 p8_4526l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4528_1, c8_4528_2, c8_4528_3, c8_4528_4, c8_4528_5, c8_4528_6, c8_4528_7, c8_4528_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4524l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4530_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4524l) (hubSubn 8 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4530 :
    hubcapFit theRedpart rf8 p8_4524l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4530_1, c8_4530_2, c8_4530_3, c8_4530_4, c8_4530_5, c8_4530_6, c8_4530_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4534r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4534r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4534r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4534r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4534r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4535_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4534r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4535 :
    hubcapFit theRedpart rf8 p8_4534r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4535_1, c8_4535_2, c8_4535_3, c8_4535_4, c8_4535_5, c8_4535_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4534l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4534l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4534l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4534l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4534l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4534l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4536_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4534l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4536 :
    hubcapFit theRedpart rf8 p8_4534l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4536_1, c8_4536_2, c8_4536_3, c8_4536_4, c8_4536_5, c8_4536_6, c8_4536_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4538_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4533l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4538 :
    hubcapFit theRedpart rf8 p8_4533l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4538_1, c8_4538_2, c8_4538_3, c8_4538_4, c8_4538_5, c8_4538_6, c8_4538_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4532l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4540_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4532l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4540 :
    hubcapFit theRedpart rf8 p8_4532l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4540_1, c8_4540_2, c8_4540_3, c8_4540_4, c8_4540_5, c8_4540_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4542l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4543_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4542l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4543 :
    hubcapFit theRedpart rf8 p8_4542l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4543_1, c8_4543_2, c8_4543_3, c8_4543_4, c8_4543_5, c8_4543_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4542r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4542r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4542r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4542r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4542r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4545_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4542r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4545 :
    hubcapFit theRedpart rf8 p8_4542r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4545_1, c8_4545_2, c8_4545_3, c8_4545_4, c8_4545_5, c8_4545_6]

end FourColor

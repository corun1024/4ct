import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 86 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4599l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4599l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4610_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4599l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4610 :
    hubcapFit theRedpart rf7 p7_4599l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4610_1, c7_4610_2, c7_4610_3, c7_4610_4, c7_4610_5, c7_4610_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4597l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4597l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4597l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4612_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4597l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4612 :
    hubcapFit theRedpart rf7 p7_4597l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4612_1, c7_4612_2, c7_4612_3, c7_4612_4, c7_4612_5, c7_4612_6, c7_4612_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4614_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4614_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4614_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4614_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4596l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4614_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4596l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4614 :
    hubcapFit theRedpart rf7 p7_4596l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4614_1, c7_4614_2, c7_4614_3, c7_4614_4, c7_4614_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4595l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4615_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4595l) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4615 :
    hubcapFit theRedpart rf7 p7_4595l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4615_1, c7_4615_2, c7_4615_3, c7_4615_4, c7_4615_5, c7_4615_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4618r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4618r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4618r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4618r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4618r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4619_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4618r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4619 :
    hubcapFit theRedpart rf7 p7_4618r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4619_1, c7_4619_2, c7_4619_3, c7_4619_4, c7_4619_5, c7_4619_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4618l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4618l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4620_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4620 :
    hubcapFit theRedpart rf7 p7_4618l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4620_1, c7_4620_2, c7_4620_3, c7_4620_4, c7_4620_5, c7_4620_6, c7_4620_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4622_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4593l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4622 :
    hubcapFit theRedpart rf7 p7_4593l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4622_1, c7_4622_2, c7_4622_3, c7_4622_4, c7_4622_5, c7_4622_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4637r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4637r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4637r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4637r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4637r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4637r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4638_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4637r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4638 :
    hubcapFit theRedpart rf7 p7_4637r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4638_1, c7_4638_2, c7_4638_3, c7_4638_4, c7_4638_5, c7_4638_6, c7_4638_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4642r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4642r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4642r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4642r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4642r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4642r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4643_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4642r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4643 :
    hubcapFit theRedpart rf7 p7_4642r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4643_1, c7_4643_2, c7_4643_3, c7_4643_4, c7_4643_5, c7_4643_6, c7_4643_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4644_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4644 :
    hubcapFit theRedpart rf7 p7_4642l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4644_1, c7_4644_2, c7_4644_3, c7_4644_4, c7_4644_5, c7_4644_6, c7_4644_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4641l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4641l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4641l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4646_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4641l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4646 :
    hubcapFit theRedpart rf7 p7_4641l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4646_1, c7_4646_2, c7_4646_3, c7_4646_4, c7_4646_5, c7_4646_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4640l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4640l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4640l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4640l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4647_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4640l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4647 :
    hubcapFit theRedpart rf7 p7_4640l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4647_1, c7_4647_2, c7_4647_3, c7_4647_4, c7_4647_5, c7_4647_6, c7_4647_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4633l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4633l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4633l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4633l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4633l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4649_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4633l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4649 :
    hubcapFit theRedpart rf7 p7_4633l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4649_1, c7_4649_2, c7_4649_3, c7_4649_4, c7_4649_5, c7_4649_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4632l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4632l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4632l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4632l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4632l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4651_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4632l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4651 :
    hubcapFit theRedpart rf7 p7_4632l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4651_1, c7_4651_2, c7_4651_3, c7_4651_4, c7_4651_5, c7_4651_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4656r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4656r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4656r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4656r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4656r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4657_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4656r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4657 :
    hubcapFit theRedpart rf7 p7_4656r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4657_1, c7_4657_2, c7_4657_3, c7_4657_4, c7_4657_5, c7_4657_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4658_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4658_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4658_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4658_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4656l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4658_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4656l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4658 :
    hubcapFit theRedpart rf7 p7_4656l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4658_1, c7_4658_2, c7_4658_3, c7_4658_4, c7_4658_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4655l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4655l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4655l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4655l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4655l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4660_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4655l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4660 :
    hubcapFit theRedpart rf7 p7_4655l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4660_1, c7_4660_2, c7_4660_3, c7_4660_4, c7_4660_5, c7_4660_6]

end FourColor

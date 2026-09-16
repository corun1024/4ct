import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 91 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4562r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4562r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4562r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4562r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4562r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4562r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4563_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4562r) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4563 :
    hubcapFit theRedpart rf8 p8_4562r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4563_1, c8_4563_2, c8_4563_3, c8_4563_4, c8_4563_5, c8_4563_6, c8_4563_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4562l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4562l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4564_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4562l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4564 :
    hubcapFit theRedpart rf8 p8_4562l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4564_1, c8_4564_2, c8_4564_3, c8_4564_4, c8_4564_5, c8_4564_6, c8_4564_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4560l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4566_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4566 :
    hubcapFit theRedpart rf8 p8_4560l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4566_1, c8_4566_2, c8_4566_3, c8_4566_4, c8_4566_5, c8_4566_6, c8_4566_7, c8_4566_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4568_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4559l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4568 :
    hubcapFit theRedpart rf8 p8_4559l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4568_1, c8_4568_2, c8_4568_3, c8_4568_4, c8_4568_5, c8_4568_6, c8_4568_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4556l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4570_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4556l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4570 :
    hubcapFit theRedpart rf8 p8_4556l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4570_1, c8_4570_2, c8_4570_3, c8_4570_4, c8_4570_5, c8_4570_6, c8_4570_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4555l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4555l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4555l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4555l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4555l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4572_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4555l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4572 :
    hubcapFit theRedpart rf8 p8_4555l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4572_1, c8_4572_2, c8_4572_3, c8_4572_4, c8_4572_5, c8_4572_6, c8_4572_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4554l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4574_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4554l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4574 :
    hubcapFit theRedpart rf8 p8_4554l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4574_1, c8_4574_2, c8_4574_3, c8_4574_4, c8_4574_5, c8_4574_6, c8_4574_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4553l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4553l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4576_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4553l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4576 :
    hubcapFit theRedpart rf8 p8_4553l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4576_1, c8_4576_2, c8_4576_3, c8_4576_4, c8_4576_5, c8_4576_6, c8_4576_7, c8_4576_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4552l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4552l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4552l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4552l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4578_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4552l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4578 :
    hubcapFit theRedpart rf8 p8_4552l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4578_1, c8_4578_2, c8_4578_3, c8_4578_4, c8_4578_5, c8_4578_6, c8_4578_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4550l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4550l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4550l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4580_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4550l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4580 :
    hubcapFit theRedpart rf8 p8_4550l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4580_1, c8_4580_2, c8_4580_3, c8_4580_4, c8_4580_5, c8_4580_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4549l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4549l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4582_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4549l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4582 :
    hubcapFit theRedpart rf8 p8_4549l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4582_1, c8_4582_2, c8_4582_3, c8_4582_4, c8_4582_5, c8_4582_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4583l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4583l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4583l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4584_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4583l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4584 :
    hubcapFit theRedpart rf8 p8_4583l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4584_1, c8_4584_2, c8_4584_3, c8_4584_4, c8_4584_5, c8_4584_6, c8_4584_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4583r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4583r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4583r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4583r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4583r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4583r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4586_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4583r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4586 :
    hubcapFit theRedpart rf8 p8_4583r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4586_1, c8_4586_2, c8_4586_3, c8_4586_4, c8_4586_5, c8_4586_6, c8_4586_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4517l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4517l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4517l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4590_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4517l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4590 :
    hubcapFit theRedpart rf8 p8_4517l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4590_1, c8_4590_2, c8_4590_3, c8_4590_4, c8_4590_5, c8_4590_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4594r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4594r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4594r) (hubSubn 8 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4595_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4594r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4595 :
    hubcapFit theRedpart rf8 p8_4594r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4595_1, c8_4595_2, c8_4595_3, c8_4595_4, c8_4595_5, c8_4595_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4594l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4594l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4594l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4596_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4594l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4596 :
    hubcapFit theRedpart rf8 p8_4594l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4596_1, c8_4596_2, c8_4596_3, c8_4596_4, c8_4596_5, c8_4596_6]

end FourColor

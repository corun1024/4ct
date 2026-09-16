import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 94 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4678l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4678l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4691_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4691 :
    hubcapFit theRedpart rf8 p8_4678l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4691_1, c8_4691_2, c8_4691_3, c8_4691_4, c8_4691_5, c8_4691_6, c8_4691_7, c8_4691_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4675l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4675l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4675l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4675l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4675l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4693_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4675l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4693 :
    hubcapFit theRedpart rf8 p8_4675l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4693_1, c8_4693_2, c8_4693_3, c8_4693_4, c8_4693_5, c8_4693_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4698r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4698r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4698r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4698r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4698r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4698r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4699_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4698r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4699 :
    hubcapFit theRedpart rf8 p8_4698r
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4699_1, c8_4699_2, c8_4699_3, c8_4699_4, c8_4699_5, c8_4699_6, c8_4699_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4698l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4698l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4698l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4698l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4700_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4698l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4700 :
    hubcapFit theRedpart rf8 p8_4698l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4700_1, c8_4700_2, c8_4700_3, c8_4700_4, c8_4700_5, c8_4700_6, c8_4700_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4697l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4697l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4697l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4697l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4697l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4697l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4697l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4702_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4697l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4702 :
    hubcapFit theRedpart rf8 p8_4697l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4702_1, c8_4702_2, c8_4702_3, c8_4702_4, c8_4702_5, c8_4702_6, c8_4702_7, c8_4702_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4696l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4696l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4696l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4696l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4696l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4704_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4696l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4704 :
    hubcapFit theRedpart rf8 p8_4696l
    (Hubcap.one 2 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4704_1, c8_4704_2, c8_4704_3, c8_4704_4, c8_4704_5, c8_4704_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4695l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4705_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4705 :
    hubcapFit theRedpart rf8 p8_4695l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4705_1, c8_4705_2, c8_4705_3, c8_4705_4, c8_4705_5, c8_4705_6, c8_4705_7, c8_4705_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4708_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4642l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4708_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4642l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4708_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4642l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4708_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4642l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4708_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4642l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4708 :
    hubcapFit theRedpart rf8 p8_4642l
    (Hubcap.one 2 5 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4708_1, c8_4708_2, c8_4708_3, c8_4708_4, c8_4708_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4724r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4724r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4724r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4724r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4724r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4725_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4724r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4725 :
    hubcapFit theRedpart rf8 p8_4724r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4725_1, c8_4725_2, c8_4725_3, c8_4725_4, c8_4725_5, c8_4725_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4731r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4731r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4731r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4731r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4731r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4731r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4732_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4731r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4732 :
    hubcapFit theRedpart rf8 p8_4731r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4732_1, c8_4732_2, c8_4732_3, c8_4732_4, c8_4732_5, c8_4732_6, c8_4732_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4731l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4731l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4731l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4731l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4731l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4733_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4733 :
    hubcapFit theRedpart rf8 p8_4731l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4733_1, c8_4733_2, c8_4733_3, c8_4733_4, c8_4733_5, c8_4733_6, c8_4733_7, c8_4733_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4735_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4730l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4735 :
    hubcapFit theRedpart rf8 p8_4730l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4735_1, c8_4735_2, c8_4735_3, c8_4735_4, c8_4735_5, c8_4735_6, c8_4735_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4729l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4729l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4729l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4729l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4729l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4737_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4729l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4737 :
    hubcapFit theRedpart rf8 p8_4729l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4737_1, c8_4737_2, c8_4737_3, c8_4737_4, c8_4737_5, c8_4737_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4728l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4728l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4728l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4738_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4728l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4738 :
    hubcapFit theRedpart rf8 p8_4728l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4738_1, c8_4738_2, c8_4738_3, c8_4738_4, c8_4738_5, c8_4738_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4744r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4744r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4744r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4744r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4744r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4745_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4744r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4745 :
    hubcapFit theRedpart rf8 p8_4744r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4745_1, c8_4745_2, c8_4745_3, c8_4745_4, c8_4745_5, c8_4745_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4744l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4744l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4746_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4744l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4746 :
    hubcapFit theRedpart rf8 p8_4744l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4746_1, c8_4746_2, c8_4746_3, c8_4746_4, c8_4746_5, c8_4746_6, c8_4746_7]

end FourColor

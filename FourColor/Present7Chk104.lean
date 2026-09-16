import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 104 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5497l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5497l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5497l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5524_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5497l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5524 :
    hubcapFit theRedpart rf7 p7_5497l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5524_1, c7_5524_2, c7_5524_3, c7_5524_4, c7_5524_5, c7_5524_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5533r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5533r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5533r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5533r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5533r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5533r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5534_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5533r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5534 :
    hubcapFit theRedpart rf7 p7_5533r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5534_1, c7_5534_2, c7_5534_3, c7_5534_4, c7_5534_5, c7_5534_6, c7_5534_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5533l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5535_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5535 :
    hubcapFit theRedpart rf7 p7_5533l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5535_1, c7_5535_2, c7_5535_3, c7_5535_4, c7_5535_5, c7_5535_6, c7_5535_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5532l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5537_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5532l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5537 :
    hubcapFit theRedpart rf7 p7_5532l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5537_1, c7_5537_2, c7_5537_3, c7_5537_4, c7_5537_5, c7_5537_6, c7_5537_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5531l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5531l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5539_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5531l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5539 :
    hubcapFit theRedpart rf7 p7_5531l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5539_1, c7_5539_2, c7_5539_3, c7_5539_4, c7_5539_5, c7_5539_6, c7_5539_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5530l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5530l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5530l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5541_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5541 :
    hubcapFit theRedpart rf7 p7_5530l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5541_1, c7_5541_2, c7_5541_3, c7_5541_4, c7_5541_5, c7_5541_6, c7_5541_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5529l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5529l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5529l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5529l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5529l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5529l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5543_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5529l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5543 :
    hubcapFit theRedpart rf7 p7_5529l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5543_1, c7_5543_2, c7_5543_3, c7_5543_4, c7_5543_5, c7_5543_6, c7_5543_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5545_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5545 :
    hubcapFit theRedpart rf7 p7_5528l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5545_1, c7_5545_2, c7_5545_3, c7_5545_4, c7_5545_5, c7_5545_6, c7_5545_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5527l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5527l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5547_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5527l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5547 :
    hubcapFit theRedpart rf7 p7_5527l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5547_1, c7_5547_2, c7_5547_3, c7_5547_4, c7_5547_5, c7_5547_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5526l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5526l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5526l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5548_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5526l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5548 :
    hubcapFit theRedpart rf7 p7_5526l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5548_1, c7_5548_2, c7_5548_3, c7_5548_4, c7_5548_5, c7_5548_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5525l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5525l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5525l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5550_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5525l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5550 :
    hubcapFit theRedpart rf7 p7_5525l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5550_1, c7_5550_2, c7_5550_3, c7_5550_4, c7_5550_5, c7_5550_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5556r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5556r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5556r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5556r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5556r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5556r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5557_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5556r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5557 :
    hubcapFit theRedpart rf7 p7_5556r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5557_1, c7_5557_2, c7_5557_3, c7_5557_4, c7_5557_5, c7_5557_6, c7_5557_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5556l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5558_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5556l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5558 :
    hubcapFit theRedpart rf7 p7_5556l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5558_1, c7_5558_2, c7_5558_3, c7_5558_4, c7_5558_5, c7_5558_6, c7_5558_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5554l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5554l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5560_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5554l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5560 :
    hubcapFit theRedpart rf7 p7_5554l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5560_1, c7_5560_2, c7_5560_3, c7_5560_4, c7_5560_5, c7_5560_6, c7_5560_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5570r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5570r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5570r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5570r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5570r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5570r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5571_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5570r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5571 :
    hubcapFit theRedpart rf7 p7_5570r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5571_1, c7_5571_2, c7_5571_3, c7_5571_4, c7_5571_5, c7_5571_6, c7_5571_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5570l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5572_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5570l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5572 :
    hubcapFit theRedpart rf7 p7_5570l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5572_1, c7_5572_2, c7_5572_3, c7_5572_4, c7_5572_5, c7_5572_6, c7_5572_7]

end FourColor

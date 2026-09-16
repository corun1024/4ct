import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 65 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3509l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3509l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3509l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3520_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3509l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3520 :
    hubcapFit theRedpart rf7 p7_3509l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3520_1, c7_3520_2, c7_3520_3, c7_3520_4, c7_3520_5, c7_3520_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3522_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3522_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3522_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3522_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3508l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3522_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3508l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3522 :
    hubcapFit theRedpart rf7 p7_3508l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3522_1, c7_3522_2, c7_3522_3, c7_3522_4, c7_3522_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3528_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3527r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3528_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3527r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3528_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3527r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3528_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3527r) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3528_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3527r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3528 :
    hubcapFit theRedpart rf7 p7_3527r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3528_1, c7_3528_2, c7_3528_3, c7_3528_4, c7_3528_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3529_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3529_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3529_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3527l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3529_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3527l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3529_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3527l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3529 :
    hubcapFit theRedpart rf7 p7_3527l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3529_1, c7_3529_2, c7_3529_3, c7_3529_4, c7_3529_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3531_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3531_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3531_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3526l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3531_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3526l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3531_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3526l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3531 :
    hubcapFit theRedpart rf7 p7_3526l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3531_1, c7_3531_2, c7_3531_3, c7_3531_4, c7_3531_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3525l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3525l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3532_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3525l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3532 :
    hubcapFit theRedpart rf7 p7_3525l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3532_1, c7_3532_2, c7_3532_3, c7_3532_4, c7_3532_5, c7_3532_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3534_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3534_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3534_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3524l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3534_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3524l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3534_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3524l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3534 :
    hubcapFit theRedpart rf7 p7_3524l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3534_1, c7_3534_2, c7_3534_3, c7_3534_4, c7_3534_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3541_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3540r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3541_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3540r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3541_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3540r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3541_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3540r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3541_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3540r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3541 :
    hubcapFit theRedpart rf7 p7_3540r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3541_1, c7_3541_2, c7_3541_3, c7_3541_4, c7_3541_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3542_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3540l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3542_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3540l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3542_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3540l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3542_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3540l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3542_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3540l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3542 :
    hubcapFit theRedpart rf7 p7_3540l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3542_1, c7_3542_2, c7_3542_3, c7_3542_4, c7_3542_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3539l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3539l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3539l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3539l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3539l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3544_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3539l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3544 :
    hubcapFit theRedpart rf7 p7_3539l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3544_1, c7_3544_2, c7_3544_3, c7_3544_4, c7_3544_5, c7_3544_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3538l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3538l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3538l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3538l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3538l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3545_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3538l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3545 :
    hubcapFit theRedpart rf7 p7_3538l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3545_1, c7_3545_2, c7_3545_3, c7_3545_4, c7_3545_5, c7_3545_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3552r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3552r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3552r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3552r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3552r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3552r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3553_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3552r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3553 :
    hubcapFit theRedpart rf7 p7_3552r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3553_1, c7_3553_2, c7_3553_3, c7_3553_4, c7_3553_5, c7_3553_6, c7_3553_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3552l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3552l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3552l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3554_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3552l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3554 :
    hubcapFit theRedpart rf7 p7_3552l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3554_1, c7_3554_2, c7_3554_3, c7_3554_4, c7_3554_5, c7_3554_6, c7_3554_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3551l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3551l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3551l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3551l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3551l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3556_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3551l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3556 :
    hubcapFit theRedpart rf7 p7_3551l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3556_1, c7_3556_2, c7_3556_3, c7_3556_4, c7_3556_5, c7_3556_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3557_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3557_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3550l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3557_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3550l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3557_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3550l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3557_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3550l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3557 :
    hubcapFit theRedpart rf7 p7_3550l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3557_1, c7_3557_2, c7_3557_3, c7_3557_4, c7_3557_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3561_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3560r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3561_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3560r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3561_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3560r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3561_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3560r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3561_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3560r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3561 :
    hubcapFit theRedpart rf7 p7_3560r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3561_1, c7_3561_2, c7_3561_3, c7_3561_4, c7_3561_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3560l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3560l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3562_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3560l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3562 :
    hubcapFit theRedpart rf7 p7_3560l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3562_1, c7_3562_2, c7_3562_3, c7_3562_4, c7_3562_5, c7_3562_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3559l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3559l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3564_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3559l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3564 :
    hubcapFit theRedpart rf7 p7_3559l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3564_1, c7_3564_2, c7_3564_3, c7_3564_4, c7_3564_5, c7_3564_6, c7_3564_7]

end FourColor

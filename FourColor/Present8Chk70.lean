import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 70 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3514l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3514l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3514l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3514l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3550_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3514l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3550 :
    hubcapFit theRedpart rf8 p8_3514l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3550_1, c8_3550_2, c8_3550_3, c8_3550_4, c8_3550_5, c8_3550_6, c8_3550_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3513l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3513l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3513l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3552_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3513l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3552 :
    hubcapFit theRedpart rf8 p8_3513l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3552_1, c8_3552_2, c8_3552_3, c8_3552_4, c8_3552_5, c8_3552_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3561r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3561r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3561r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3561r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3561r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3562_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3561r) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3562 :
    hubcapFit theRedpart rf8 p8_3561r
    (Hubcap.one 1 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3562_1, c8_3562_2, c8_3562_3, c8_3562_4, c8_3562_5, c8_3562_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3561l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3561l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3561l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3561l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3563_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3561l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3563 :
    hubcapFit theRedpart rf8 p8_3561l
    (Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3563_1, c8_3563_2, c8_3563_3, c8_3563_4, c8_3563_5, c8_3563_6, c8_3563_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3560l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3560l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3560l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3560l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3565_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3560l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3565 :
    hubcapFit theRedpart rf8 p8_3560l
    (Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3565_1, c8_3565_2, c8_3565_3, c8_3565_4, c8_3565_5, c8_3565_6, c8_3565_7, c8_3565_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3558l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3558l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3558l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3567_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3558l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3567 :
    hubcapFit theRedpart rf8 p8_3558l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3567_1, c8_3567_2, c8_3567_3, c8_3567_4, c8_3567_5, c8_3567_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3557l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3557l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3569_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3557l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3569 :
    hubcapFit theRedpart rf8 p8_3557l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3569_1, c8_3569_2, c8_3569_3, c8_3569_4, c8_3569_5, c8_3569_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3575r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3575r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3575r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3575r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3575r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3575r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3576_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3575r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3576 :
    hubcapFit theRedpart rf8 p8_3575r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3576_1, c8_3576_2, c8_3576_3, c8_3576_4, c8_3576_5, c8_3576_6, c8_3576_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3575l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3575l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3575l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3575l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3575l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3577_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3575l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3577 :
    hubcapFit theRedpart rf8 p8_3575l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3577_1, c8_3577_2, c8_3577_3, c8_3577_4, c8_3577_5, c8_3577_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3574l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3574l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3574l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3579_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3574l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3579 :
    hubcapFit theRedpart rf8 p8_3574l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3579_1, c8_3579_2, c8_3579_3, c8_3579_4, c8_3579_5, c8_3579_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3572l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3572l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3572l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3572l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3581_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3572l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3581 :
    hubcapFit theRedpart rf8 p8_3572l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3581_1, c8_3581_2, c8_3581_3, c8_3581_4, c8_3581_5, c8_3581_6, c8_3581_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3571l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3583_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3571l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3583 :
    hubcapFit theRedpart rf8 p8_3571l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3583_1, c8_3583_2, c8_3583_3, c8_3583_4, c8_3583_5, c8_3583_6, c8_3583_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3553l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3553l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3585_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3553l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3585 :
    hubcapFit theRedpart rf8 p8_3553l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3585_1, c8_3585_2, c8_3585_3, c8_3585_4, c8_3585_5, c8_3585_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3511l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3511l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3511l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3588_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3511l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3588 :
    hubcapFit theRedpart rf8 p8_3511l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3588_1, c8_3588_2, c8_3588_3, c8_3588_4, c8_3588_5, c8_3588_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3510l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3510l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3510l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3510l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3510l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3589_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3510l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3589 :
    hubcapFit theRedpart rf8 p8_3510l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3589_1, c8_3589_2, c8_3589_3, c8_3589_4, c8_3589_5, c8_3589_6, c8_3589_7, c8_3589_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3601r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3601r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3601r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3601r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3601r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3601r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3602_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3601r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3602 :
    hubcapFit theRedpart rf8 p8_3601r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3602_1, c8_3602_2, c8_3602_3, c8_3602_4, c8_3602_5, c8_3602_6, c8_3602_7]

end FourColor

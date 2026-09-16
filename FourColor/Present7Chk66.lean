import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 66 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3571r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3571r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3571r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3571r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3571r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3572_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3571r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3572 :
    hubcapFit theRedpart rf7 p7_3571r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3572_1, c7_3572_2, c7_3572_3, c7_3572_4, c7_3572_5, c7_3572_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3573_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3573_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3573_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3573_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3571l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3573_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3571l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3573 :
    hubcapFit theRedpart rf7 p7_3571l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3573_1, c7_3573_2, c7_3573_3, c7_3573_4, c7_3573_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3569l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3569l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3569l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3569l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3575_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3569l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3575 :
    hubcapFit theRedpart rf7 p7_3569l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3575_1, c7_3575_2, c7_3575_3, c7_3575_4, c7_3575_5, c7_3575_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3568l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3568l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3568l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3568l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3568l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3568l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3577_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3568l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3577 :
    hubcapFit theRedpart rf7 p7_3568l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3577_1, c7_3577_2, c7_3577_3, c7_3577_4, c7_3577_5, c7_3577_6, c7_3577_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3567l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3579_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3567l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3579 :
    hubcapFit theRedpart rf7 p7_3567l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3579_1, c7_3579_2, c7_3579_3, c7_3579_4, c7_3579_5, c7_3579_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3588r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3588r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3588r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3588r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3588r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3589_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3588r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3589 :
    hubcapFit theRedpart rf7 p7_3588r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3589_1, c7_3589_2, c7_3589_3, c7_3589_4, c7_3589_5, c7_3589_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3588l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3588l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3588l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3588l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3588l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3590_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3588l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3590 :
    hubcapFit theRedpart rf7 p7_3588l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3590_1, c7_3590_2, c7_3590_3, c7_3590_4, c7_3590_5, c7_3590_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3592_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3587l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3592_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3587l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3592_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3587l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3592_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3587l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3592_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3587l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3592 :
    hubcapFit theRedpart rf7 p7_3587l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3592_1, c7_3592_2, c7_3592_3, c7_3592_4, c7_3592_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3598r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3598r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3598r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3598r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3598r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3599_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3598r) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3599 :
    hubcapFit theRedpart rf7 p7_3598r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3599_1, c7_3599_2, c7_3599_3, c7_3599_4, c7_3599_5, c7_3599_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3598l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3598l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3598l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3598l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3598l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3600_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3598l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3600 :
    hubcapFit theRedpart rf7 p7_3598l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3600_1, c7_3600_2, c7_3600_3, c7_3600_4, c7_3600_5, c7_3600_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3597l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3597l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3597l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3602_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3597l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3602 :
    hubcapFit theRedpart rf7 p7_3597l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3602_1, c7_3602_2, c7_3602_3, c7_3602_4, c7_3602_5, c7_3602_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3596l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3596l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3596l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3596l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3603_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3596l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3603 :
    hubcapFit theRedpart rf7 p7_3596l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3603_1, c7_3603_2, c7_3603_3, c7_3603_4, c7_3603_5, c7_3603_6, c7_3603_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3595l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3595l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3605_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3605 :
    hubcapFit theRedpart rf7 p7_3595l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3605_1, c7_3605_2, c7_3605_3, c7_3605_4, c7_3605_5, c7_3605_6, c7_3605_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3594l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3594l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3594l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3607_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3594l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3607 :
    hubcapFit theRedpart rf7 p7_3594l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3607_1, c7_3607_2, c7_3607_3, c7_3607_4, c7_3607_5, c7_3607_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3593l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3608_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3593l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3608 :
    hubcapFit theRedpart rf7 p7_3593l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3608_1, c7_3608_2, c7_3608_3, c7_3608_4, c7_3608_5, c7_3608_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3616r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3616r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3616r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3616r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3616r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3616r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3617_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3616r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3617 :
    hubcapFit theRedpart rf7 p7_3616r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3617_1, c7_3617_2, c7_3617_3, c7_3617_4, c7_3617_5, c7_3617_6, c7_3617_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3618_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3616l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3618 :
    hubcapFit theRedpart rf7 p7_3616l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3618_1, c7_3618_2, c7_3618_3, c7_3618_4, c7_3618_5, c7_3618_6]

end FourColor

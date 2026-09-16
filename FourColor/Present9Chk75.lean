import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 75 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3511l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3511l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3511l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3511l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3536_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3536 :
    hubcapFit theRedpart rf9 p9_3511l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3536_1, c9_3536_2, c9_3536_3, c9_3536_4, c9_3536_5, c9_3536_6, c9_3536_7, c9_3536_8, c9_3536_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3555r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3555r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3555r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3555r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3555r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3555r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3556_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3555r) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3556 :
    hubcapFit theRedpart rf9 p9_3555r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3556_1, c9_3556_2, c9_3556_3, c9_3556_4, c9_3556_5, c9_3556_6, c9_3556_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3555l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3555l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3555l) (hubSubn 9 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3557_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3555l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3557 :
    hubcapFit theRedpart rf9 p9_3555l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3557_1, c9_3557_2, c9_3557_3, c9_3557_4, c9_3557_5, c9_3557_6, c9_3557_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3554l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3554l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3554l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3559_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3554l) (hubSubn 9 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3559 :
    hubcapFit theRedpart rf9 p9_3554l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3559_1, c9_3559_2, c9_3559_3, c9_3559_4, c9_3559_5, c9_3559_6, c9_3559_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3568r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3568r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3568r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3568r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3568r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3568r) (hubSubn 9 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3569_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3568r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3569 :
    hubcapFit theRedpart rf9 p9_3568r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3569_1, c9_3569_2, c9_3569_3, c9_3569_4, c9_3569_5, c9_3569_6, c9_3569_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3566l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3566l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3566l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3566l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3566l) (hubSubn 9 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3571_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3566l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3571 :
    hubcapFit theRedpart rf9 p9_3566l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3571_1, c9_3571_2, c9_3571_3, c9_3571_4, c9_3571_5, c9_3571_6, c9_3571_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3573r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3573r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3573r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3573r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3573r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3573r) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3574_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3573r) (hubSubn 9 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3574 :
    hubcapFit theRedpart rf9 p9_3573r
    (Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3574_1, c9_3574_2, c9_3574_3, c9_3574_4, c9_3574_5, c9_3574_6, c9_3574_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3573l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3573l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3573l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3573l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3573l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3573l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3573l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3575_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3573l) (hubSubn 9 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3575 :
    hubcapFit theRedpart rf9 p9_3573l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3575_1, c9_3575_2, c9_3575_3, c9_3575_4, c9_3575_5, c9_3575_6, c9_3575_7, c9_3575_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3581r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3581r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3581r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3581r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3581r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3581r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3581r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3582_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3581r) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3582 :
    hubcapFit theRedpart rf9 p9_3581r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3582_1, c9_3582_2, c9_3582_3, c9_3582_4, c9_3582_5, c9_3582_6, c9_3582_7, c9_3582_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3581l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3581l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3581l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3581l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3583_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3581l) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3583 :
    hubcapFit theRedpart rf9 p9_3581l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3583_1, c9_3583_2, c9_3583_3, c9_3583_4, c9_3583_5, c9_3583_6, c9_3583_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3579l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3579l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3579l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3579l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3579l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3579l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3585_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3579l) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3585 :
    hubcapFit theRedpart rf9 p9_3579l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3585_1, c9_3585_2, c9_3585_3, c9_3585_4, c9_3585_5, c9_3585_6, c9_3585_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3578l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3578l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3578l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3578l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3578l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3587_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3578l) (hubSubn 9 8 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3587 :
    hubcapFit theRedpart rf9 p9_3578l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3587_1, c9_3587_2, c9_3587_3, c9_3587_4, c9_3587_5, c9_3587_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3563l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3563l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3563l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3563l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3563l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3589_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3563l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3589 :
    hubcapFit theRedpart rf9 p9_3563l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3589_1, c9_3589_2, c9_3589_3, c9_3589_4, c9_3589_5, c9_3589_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3562l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3562l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3591_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3562l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3591 :
    hubcapFit theRedpart rf9 p9_3562l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3591_1, c9_3591_2, c9_3591_3, c9_3591_4, c9_3591_5, c9_3591_6, c9_3591_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3561l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3561l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3561l) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3561l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3593_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3561l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3593 :
    hubcapFit theRedpart rf9 p9_3561l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3593_1, c9_3593_2, c9_3593_3, c9_3593_4, c9_3593_5, c9_3593_6]

end FourColor

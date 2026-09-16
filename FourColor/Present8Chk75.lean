import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 75 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3782l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3782l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3782l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3782l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3782l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3782l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3794_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3782l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3794 :
    hubcapFit theRedpart rf8 p8_3782l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3794_1, c8_3794_2, c8_3794_3, c8_3794_4, c8_3794_5, c8_3794_6, c8_3794_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3781l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3781l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3781l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3781l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3781l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3781l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3796_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3781l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3796 :
    hubcapFit theRedpart rf8 p8_3781l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3796_1, c8_3796_2, c8_3796_3, c8_3796_4, c8_3796_5, c8_3796_6, c8_3796_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3780l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3780l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3798_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3798 :
    hubcapFit theRedpart rf8 p8_3780l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3798_1, c8_3798_2, c8_3798_3, c8_3798_4, c8_3798_5, c8_3798_6, c8_3798_7, c8_3798_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3779l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3779l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3779l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3779l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3779l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3800_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3779l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3800 :
    hubcapFit theRedpart rf8 p8_3779l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3800_1, c8_3800_2, c8_3800_3, c8_3800_4, c8_3800_5, c8_3800_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3778l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3778l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3778l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3778l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3778l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3801_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3801 :
    hubcapFit theRedpart rf8 p8_3778l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3801_1, c8_3801_2, c8_3801_3, c8_3801_4, c8_3801_5, c8_3801_6, c8_3801_7, c8_3801_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3776l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3776l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3803_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3776l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3803 :
    hubcapFit theRedpart rf8 p8_3776l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3803_1, c8_3803_2, c8_3803_3, c8_3803_4, c8_3803_5, c8_3803_6, c8_3803_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3775l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3775l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3775l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3805_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3805 :
    hubcapFit theRedpart rf8 p8_3775l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3805_1, c8_3805_2, c8_3805_3, c8_3805_4, c8_3805_5, c8_3805_6, c8_3805_7, c8_3805_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3774l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3774l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3774l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3774l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3774l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3774l) (hubSubn 8 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3807_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3774l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3807 :
    hubcapFit theRedpart rf8 p8_3774l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3807_1, c8_3807_2, c8_3807_3, c8_3807_4, c8_3807_5, c8_3807_6, c8_3807_7, c8_3807_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3773l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3773l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3773l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3773l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3773l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3809_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3773l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3809 :
    hubcapFit theRedpart rf8 p8_3773l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3809_1, c8_3809_2, c8_3809_3, c8_3809_4, c8_3809_5, c8_3809_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3772l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3772l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3772l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3772l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3810_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3772l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3810 :
    hubcapFit theRedpart rf8 p8_3772l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3810_1, c8_3810_2, c8_3810_3, c8_3810_4, c8_3810_5, c8_3810_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3825r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3825r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3825r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3825r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3825r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3825r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3826_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3825r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3826 :
    hubcapFit theRedpart rf8 p8_3825r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3826_1, c8_3826_2, c8_3826_3, c8_3826_4, c8_3826_5, c8_3826_6, c8_3826_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3825l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3825l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3827_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3827 :
    hubcapFit theRedpart rf8 p8_3825l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3827_1, c8_3827_2, c8_3827_3, c8_3827_4, c8_3827_5, c8_3827_6, c8_3827_7, c8_3827_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3824l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3824l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3824l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3824l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3829_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3824l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3829 :
    hubcapFit theRedpart rf8 p8_3824l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3829_1, c8_3829_2, c8_3829_3, c8_3829_4, c8_3829_5, c8_3829_6, c8_3829_7, c8_3829_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3823l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3823l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3823l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3831_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3823l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3831 :
    hubcapFit theRedpart rf8 p8_3823l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3831_1, c8_3831_2, c8_3831_3, c8_3831_4, c8_3831_5, c8_3831_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3822l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3822l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3822l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3832_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3822l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3832 :
    hubcapFit theRedpart rf8 p8_3822l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3832_1, c8_3832_2, c8_3832_3, c8_3832_4, c8_3832_5, c8_3832_6]

end FourColor

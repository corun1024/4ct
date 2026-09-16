import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 75 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4006l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4006l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4006l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4030_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4006l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4030 :
    hubcapFit theRedpart rf7 p7_4006l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4030_1, c7_4030_2, c7_4030_3, c7_4030_4, c7_4030_5, c7_4030_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4005l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4005l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4005l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4005l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4005l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4031_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4005l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4031 :
    hubcapFit theRedpart rf7 p7_4005l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4031_1, c7_4031_2, c7_4031_3, c7_4031_4, c7_4031_5, c7_4031_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4004l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4004l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4004l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4004l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4004l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4033_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4004l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4033 :
    hubcapFit theRedpart rf7 p7_4004l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4033_1, c7_4033_2, c7_4033_3, c7_4033_4, c7_4033_5, c7_4033_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4039r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4039r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4039r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4039r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4039r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4040_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4039r) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4040 :
    hubcapFit theRedpart rf7 p7_4039r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4040_1, c7_4040_2, c7_4040_3, c7_4040_4, c7_4040_5, c7_4040_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4039l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4039l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4039l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4039l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4039l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4041_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4039l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4041 :
    hubcapFit theRedpart rf7 p7_4039l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4041_1, c7_4041_2, c7_4041_3, c7_4041_4, c7_4041_5, c7_4041_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4038l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4038l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4038l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4038l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4038l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4043_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4038l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4043 :
    hubcapFit theRedpart rf7 p7_4038l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4043_1, c7_4043_2, c7_4043_3, c7_4043_4, c7_4043_5, c7_4043_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4037l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4037l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4037l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4044_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4037l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4044 :
    hubcapFit theRedpart rf7 p7_4037l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4044_1, c7_4044_2, c7_4044_3, c7_4044_4, c7_4044_5, c7_4044_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4036l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4036l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4036l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4036l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4036l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4046_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4036l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4046 :
    hubcapFit theRedpart rf7 p7_4036l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4046_1, c7_4046_2, c7_4046_3, c7_4046_4, c7_4046_5, c7_4046_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4035l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4035l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4035l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4035l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4035l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4047_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4035l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4047 :
    hubcapFit theRedpart rf7 p7_4035l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4047_1, c7_4047_2, c7_4047_3, c7_4047_4, c7_4047_5, c7_4047_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4002l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4002l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4002l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4002l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4002l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4050_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4002l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4050 :
    hubcapFit theRedpart rf7 p7_4002l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4050_1, c7_4050_2, c7_4050_3, c7_4050_4, c7_4050_5, c7_4050_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4001l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4001l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4051_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4001l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4051 :
    hubcapFit theRedpart rf7 p7_4001l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4051_1, c7_4051_2, c7_4051_3, c7_4051_4, c7_4051_5, c7_4051_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4000l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4053_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4000l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4053 :
    hubcapFit theRedpart rf7 p7_4000l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4053_1, c7_4053_2, c7_4053_3, c7_4053_4, c7_4053_5, c7_4053_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3999l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3999l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3999l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3999l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4054_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3999l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4054 :
    hubcapFit theRedpart rf7 p7_3999l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4054_1, c7_4054_2, c7_4054_3, c7_4054_4, c7_4054_5, c7_4054_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3998l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3998l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3998l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3998l) (hubSubn 7 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3998l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4056_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3998l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4056 :
    hubcapFit theRedpart rf7 p7_3998l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4056_1, c7_4056_2, c7_4056_3, c7_4056_4, c7_4056_5, c7_4056_6, c7_4056_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4069r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4069r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4069r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4069r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4069r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4069r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4070_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4069r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4070 :
    hubcapFit theRedpart rf7 p7_4069r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4070_1, c7_4070_2, c7_4070_3, c7_4070_4, c7_4070_5, c7_4070_6, c7_4070_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4069l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4069l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4069l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4069l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4069l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4071_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4069l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4071 :
    hubcapFit theRedpart rf7 p7_4069l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4071_1, c7_4071_2, c7_4071_3, c7_4071_4, c7_4071_5, c7_4071_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4068l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4068l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4068l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4068l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4073_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4068l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4073 :
    hubcapFit theRedpart rf7 p7_4068l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4073_1, c7_4073_2, c7_4073_3, c7_4073_4, c7_4073_5, c7_4073_6]

end FourColor

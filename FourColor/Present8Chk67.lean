import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 67 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3399l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3399l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3399l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3399l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3399l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3399l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3401_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3399l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3401 :
    hubcapFit theRedpart rf8 p8_3399l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3401_1, c8_3401_2, c8_3401_3, c8_3401_4, c8_3401_5, c8_3401_6, c8_3401_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3398l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3398l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3398l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3398l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3398l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3398l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3403_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3398l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3403 :
    hubcapFit theRedpart rf8 p8_3398l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3403_1, c8_3403_2, c8_3403_3, c8_3403_4, c8_3403_5, c8_3403_6, c8_3403_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3386l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3386l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3386l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3386l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3406_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3386l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3406 :
    hubcapFit theRedpart rf8 p8_3386l
    (Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3406_1, c8_3406_2, c8_3406_3, c8_3406_4, c8_3406_5, c8_3406_6, c8_3406_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3385l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3385l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3385l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3385l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3385l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3385l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3408_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3385l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3408 :
    hubcapFit theRedpart rf8 p8_3385l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3408_1, c8_3408_2, c8_3408_3, c8_3408_4, c8_3408_5, c8_3408_6, c8_3408_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3384l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3384l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3384l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3384l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3384l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3410_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3384l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3410 :
    hubcapFit theRedpart rf8 p8_3384l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3410_1, c8_3410_2, c8_3410_3, c8_3410_4, c8_3410_5, c8_3410_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3383l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3383l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3383l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3411_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3383l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3411 :
    hubcapFit theRedpart rf8 p8_3383l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3411_1, c8_3411_2, c8_3411_3, c8_3411_4, c8_3411_5, c8_3411_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3419r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3419r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3419r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3419r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3419r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3419r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3420_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3419r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3420 :
    hubcapFit theRedpart rf8 p8_3419r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3420_1, c8_3420_2, c8_3420_3, c8_3420_4, c8_3420_5, c8_3420_6, c8_3420_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3419l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3419l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3419l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3421_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3419l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3421 :
    hubcapFit theRedpart rf8 p8_3419l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3421_1, c8_3421_2, c8_3421_3, c8_3421_4, c8_3421_5, c8_3421_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3418l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3418l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3423_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3418l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3423 :
    hubcapFit theRedpart rf8 p8_3418l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3423_1, c8_3423_2, c8_3423_3, c8_3423_4, c8_3423_5, c8_3423_6, c8_3423_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3417l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3425_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3417l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3425 :
    hubcapFit theRedpart rf8 p8_3417l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3425_1, c8_3425_2, c8_3425_3, c8_3425_4, c8_3425_5, c8_3425_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3416l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3416l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3416l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3416l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3426_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3416l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3426 :
    hubcapFit theRedpart rf8 p8_3416l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3426_1, c8_3426_2, c8_3426_3, c8_3426_4, c8_3426_5, c8_3426_6, c8_3426_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3428_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3415l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3428 :
    hubcapFit theRedpart rf8 p8_3415l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3428_1, c8_3428_2, c8_3428_3, c8_3428_4, c8_3428_5, c8_3428_6, c8_3428_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3381l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3381l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3381l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3381l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3381l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3381l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3430_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3381l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3430 :
    hubcapFit theRedpart rf8 p8_3381l
    (Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3430_1, c8_3430_2, c8_3430_3, c8_3430_4, c8_3430_5, c8_3430_6, c8_3430_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3380l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3380l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3380l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3380l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3380l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3380l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3432_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3380l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3432 :
    hubcapFit theRedpart rf8 p8_3380l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3432_1, c8_3432_2, c8_3432_3, c8_3432_4, c8_3432_5, c8_3432_6, c8_3432_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3450r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3450r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3450r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3450r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3450r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3450r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3450r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3451_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3450r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3451 :
    hubcapFit theRedpart rf8 p8_3450r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3451_1, c8_3451_2, c8_3451_3, c8_3451_4, c8_3451_5, c8_3451_6, c8_3451_7, c8_3451_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3450l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3450l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3450l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3450l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3450l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3450l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3452_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3450l) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3452 :
    hubcapFit theRedpart rf8 p8_3450l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3452_1, c8_3452_2, c8_3452_3, c8_3452_4, c8_3452_5, c8_3452_6, c8_3452_7]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 9 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_368l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_368l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_368l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_368l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_368l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_400_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_368l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_400 :
    hubcapFit theRedpart rf9 p9_368l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.two 5 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_400_1, c9_400_2, c9_400_3, c9_400_4, c9_400_5, c9_400_6, c9_400_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_406r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_406r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_406r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_406r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_406r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_406r) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_407_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_406r) (hubSubn 9 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_407 :
    hubcapFit theRedpart rf9 p9_406r
    (Hubcap.one 0 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_407_1, c9_407_2, c9_407_3, c9_407_4, c9_407_5, c9_407_6, c9_407_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_406l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_406l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_406l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_406l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_406l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_406l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_406l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_408_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_406l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_408 :
    hubcapFit theRedpart rf9 p9_406l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_408_1, c9_408_2, c9_408_3, c9_408_4, c9_408_5, c9_408_6, c9_408_7, c9_408_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_405l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_405l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_405l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_405l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_405l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_410_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_405l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_410 :
    hubcapFit theRedpart rf9 p9_405l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_410_1, c9_410_2, c9_410_3, c9_410_4, c9_410_5, c9_410_6, c9_410_7, c9_410_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_404l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_404l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_404l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_404l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_412_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_404l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_412 :
    hubcapFit theRedpart rf9 p9_404l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_412_1, c9_412_2, c9_412_3, c9_412_4, c9_412_5, c9_412_6, c9_412_7, c9_412_8, c9_412_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_403l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_403l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_403l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_403l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_403l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_403l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_403l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_414_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_403l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_414 :
    hubcapFit theRedpart rf9 p9_403l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_414_1, c9_414_2, c9_414_3, c9_414_4, c9_414_5, c9_414_6, c9_414_7, c9_414_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_428r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_429_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_428r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_429 :
    hubcapFit theRedpart rf9 p9_428r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_429_1, c9_429_2, c9_429_3, c9_429_4, c9_429_5, c9_429_6, c9_429_7, c9_429_8, c9_429_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_428l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_428l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_428l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_430_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_428l) (hubSubn 9 8 7) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_430 :
    hubcapFit theRedpart rf9 p9_428l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_430_1, c9_430_2, c9_430_3, c9_430_4, c9_430_5, c9_430_6, c9_430_7, c9_430_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_427l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_427l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_427l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_427l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_432_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_427l) (hubSubn 9 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_432 :
    hubcapFit theRedpart rf9 p9_427l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_432_1, c9_432_2, c9_432_3, c9_432_4, c9_432_5, c9_432_6, c9_432_7, c9_432_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_425l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_434_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_425l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_434 :
    hubcapFit theRedpart rf9 p9_425l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_434_1, c9_434_2, c9_434_3, c9_434_4, c9_434_5, c9_434_6, c9_434_7, c9_434_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_436_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_424l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_436 :
    hubcapFit theRedpart rf9 p9_424l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_436_1, c9_436_2, c9_436_3, c9_436_4, c9_436_5, c9_436_6, c9_436_7, c9_436_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_422l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_422l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_422l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_422l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_438_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_422l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_438 :
    hubcapFit theRedpart rf9 p9_422l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_438_1, c9_438_2, c9_438_3, c9_438_4, c9_438_5, c9_438_6, c9_438_7, c9_438_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_420l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_420l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_420l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_420l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_420l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_420l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_420l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_440_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_420l) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_440 :
    hubcapFit theRedpart rf9 p9_420l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_440_1, c9_440_2, c9_440_3, c9_440_4, c9_440_5, c9_440_6, c9_440_7, c9_440_8]

end FourColor

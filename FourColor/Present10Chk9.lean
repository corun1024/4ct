import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 9 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_433l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_433l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_433l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_433l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_433l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_433l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_433l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_433l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_444_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_433l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_444 :
    hubcapFit theRedpart rf10 p10_433l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_444_1, c10_444_2, c10_444_3, c10_444_4, c10_444_5, c10_444_6, c10_444_7, c10_444_8, c10_444_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_432l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_432l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_432l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_432l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_446_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_446 :
    hubcapFit theRedpart rf10 p10_432l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_446_1, c10_446_2, c10_446_3, c10_446_4, c10_446_5, c10_446_6, c10_446_7, c10_446_8, c10_446_9, c10_446_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_425l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_425l) (hubSubn 10 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_425l) (hubSubn 10 7 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_449_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_425l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_449 :
    hubcapFit theRedpart rf10 p10_425l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 1 7 8 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_449_1, c10_449_2, c10_449_3, c10_449_4, c10_449_5, c10_449_6, c10_449_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_451_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_451 :
    hubcapFit theRedpart rf10 p10_424l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 0 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_451_1, c10_451_2, c10_451_3, c10_451_4, c10_451_5, c10_451_6, c10_451_7, c10_451_8, c10_451_9, c10_451_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_423l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_423l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_423l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_423l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_423l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_453_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_423l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_453 :
    hubcapFit theRedpart rf10 p10_423l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_453_1, c10_453_2, c10_453_3, c10_453_4, c10_453_5, c10_453_6, c10_453_7, c10_453_8, c10_453_9, c10_453_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_422l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_422l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_422l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_422l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_422l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_422l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_455_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_422l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_455 :
    hubcapFit theRedpart rf10 p10_422l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_455_1, c10_455_2, c10_455_3, c10_455_4, c10_455_5, c10_455_6, c10_455_7, c10_455_8, c10_455_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_477r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_477r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_477r) (hubSubn 10 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_478_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_477r) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_478 :
    hubcapFit theRedpart rf10 p10_477r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_478_1, c10_478_2, c10_478_3, c10_478_4, c10_478_5, c10_478_6, c10_478_7, c10_478_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_477l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_479_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_477l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_479 :
    hubcapFit theRedpart rf10 p10_477l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_479_1, c10_479_2, c10_479_3, c10_479_4, c10_479_5, c10_479_6, c10_479_7, c10_479_8, c10_479_9, c10_479_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_475l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_482_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_475l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_482 :
    hubcapFit theRedpart rf10 p10_475l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_482_1, c10_482_2, c10_482_3, c10_482_4, c10_482_5, c10_482_6, c10_482_7, c10_482_8, c10_482_9, c10_482_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_474l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_484_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_474l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_484 :
    hubcapFit theRedpart rf10 p10_474l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_484_1, c10_484_2, c10_484_3, c10_484_4, c10_484_5, c10_484_6, c10_484_7, c10_484_8, c10_484_9, c10_484_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_472l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_487_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_472l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_487 :
    hubcapFit theRedpart rf10 p10_472l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_487_1, c10_487_2, c10_487_3, c10_487_4, c10_487_5, c10_487_6, c10_487_7, c10_487_8, c10_487_9, c10_487_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_469l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_469l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_469l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_489_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_469l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_489 :
    hubcapFit theRedpart rf10 p10_469l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_489_1, c10_489_2, c10_489_3, c10_489_4, c10_489_5, c10_489_6, c10_489_7, c10_489_8, c10_489_9]

end FourColor

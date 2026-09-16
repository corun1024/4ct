import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 63 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3409_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3398l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3409_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3398l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3409_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3398l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3409_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3398l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3409_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3398l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3409 :
    hubcapFit theRedpart rf7 p7_3398l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3409_1, c7_3409_2, c7_3409_3, c7_3409_4, c7_3409_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3413r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3413r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3413r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3413r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3413r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3414_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3413r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3414 :
    hubcapFit theRedpart rf7 p7_3413r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3414_1, c7_3414_2, c7_3414_3, c7_3414_4, c7_3414_5, c7_3414_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3413l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3415_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3413l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3415 :
    hubcapFit theRedpart rf7 p7_3413l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3415_1, c7_3415_2, c7_3415_3, c7_3415_4, c7_3415_5, c7_3415_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3412l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3412l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3412l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3412l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3417_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3412l) (hubSubn 7 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3417 :
    hubcapFit theRedpart rf7 p7_3412l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3417_1, c7_3417_2, c7_3417_3, c7_3417_4, c7_3417_5, c7_3417_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3418_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3411l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3418 :
    hubcapFit theRedpart rf7 p7_3411l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3418_1, c7_3418_2, c7_3418_3, c7_3418_4, c7_3418_5, c7_3418_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3425r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3425r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3425r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3425r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3425r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3426_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3425r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3426 :
    hubcapFit theRedpart rf7 p7_3425r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3426_1, c7_3426_2, c7_3426_3, c7_3426_4, c7_3426_5, c7_3426_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3425l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3425l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3427_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3425l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3427 :
    hubcapFit theRedpart rf7 p7_3425l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3427_1, c7_3427_2, c7_3427_3, c7_3427_4, c7_3427_5, c7_3427_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3424l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3429_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3424l) (hubSubn 7 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3429 :
    hubcapFit theRedpart rf7 p7_3424l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3429_1, c7_3429_2, c7_3429_3, c7_3429_4, c7_3429_5, c7_3429_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3423l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3423l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3423l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3430_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3423l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3430 :
    hubcapFit theRedpart rf7 p7_3423l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3430_1, c7_3430_2, c7_3430_3, c7_3430_4, c7_3430_5, c7_3430_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3432_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3432_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3432_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3422l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3432_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3422l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3432_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3422l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3432 :
    hubcapFit theRedpart rf7 p7_3422l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3432_1, c7_3432_2, c7_3432_3, c7_3432_4, c7_3432_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3449r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3449r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3449r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3449r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3449r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3450_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3449r) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3450 :
    hubcapFit theRedpart rf7 p7_3449r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3450_1, c7_3450_2, c7_3450_3, c7_3450_4, c7_3450_5, c7_3450_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3449l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3449l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3449l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3449l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3451_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3451 :
    hubcapFit theRedpart rf7 p7_3449l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3451_1, c7_3451_2, c7_3451_3, c7_3451_4, c7_3451_5, c7_3451_6, c7_3451_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3453_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3453_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3453_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3453_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3448l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3453_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3448l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3453 :
    hubcapFit theRedpart rf7 p7_3448l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3453_1, c7_3453_2, c7_3453_3, c7_3453_4, c7_3453_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3454_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3454_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3454_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3447l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3454_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3447l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3454_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3447l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3454 :
    hubcapFit theRedpart rf7 p7_3447l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3454_1, c7_3454_2, c7_3454_3, c7_3454_4, c7_3454_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3456_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3456_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3456_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3456_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3446l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3456_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3446l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3456 :
    hubcapFit theRedpart rf7 p7_3446l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3456_1, c7_3456_2, c7_3456_3, c7_3456_4, c7_3456_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3468_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3467r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3468_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3467r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3468_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3467r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3468_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3467r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3468_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3467r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3468 :
    hubcapFit theRedpart rf7 p7_3467r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3468_1, c7_3468_2, c7_3468_3, c7_3468_4, c7_3468_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3469_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3467l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3469_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3467l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3469_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3467l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3469_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3467l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3469_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3467l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3469 :
    hubcapFit theRedpart rf7 p7_3467l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3469_1, c7_3469_2, c7_3469_3, c7_3469_4, c7_3469_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3480r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3480r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3480r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3480r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3480r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3481_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3480r) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3481 :
    hubcapFit theRedpart rf7 p7_3480r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3481_1, c7_3481_2, c7_3481_3, c7_3481_4, c7_3481_5, c7_3481_6]

end FourColor

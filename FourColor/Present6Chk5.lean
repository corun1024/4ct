import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 5 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_403_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_401l) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_403_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_401l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_403_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_401l) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_403 :
    hubcapFit theRedpart rf6 p6_401l
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_403_1, c6_403_2, c6_403_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_406_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_405r) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_406_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_405r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_406_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_405r) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_406 :
    hubcapFit theRedpart rf6 p6_405r
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_406_1, c6_406_2, c6_406_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_407_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_405l) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_407_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_405l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_407_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_405l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_407 :
    hubcapFit theRedpart rf6 p6_405l
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_407_1, c6_407_2, c6_407_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_409_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_399l) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_409_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_399l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_409_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_399l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_409 :
    hubcapFit theRedpart rf6 p6_399l
    (Hubcap.two 0 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_409_1, c6_409_2, c6_409_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_413_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_412r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_413_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_412r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_413_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_412r) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_413 :
    hubcapFit theRedpart rf6 p6_412r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_413_1, c6_413_2, c6_413_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_414_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_412l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_414_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_412l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_414_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_412l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_414 :
    hubcapFit theRedpart rf6 p6_412l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_414_1, c6_414_2, c6_414_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_417_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_416r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_417_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_416r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_417_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_416r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_417 :
    hubcapFit theRedpart rf6 p6_416r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_417_1, c6_417_2, c6_417_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_418_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_416l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_418_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_416l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_418_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_416l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_418 :
    hubcapFit theRedpart rf6 p6_416l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_418_1, c6_418_2, c6_418_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_420_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_410l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_420_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_410l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_420_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_410l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_420 :
    hubcapFit theRedpart rf6 p6_410l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_420_1, c6_420_2, c6_420_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_426_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_425r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_426_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_425r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_426_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_425r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_426 :
    hubcapFit theRedpart rf6 p6_425r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_426_1, c6_426_2, c6_426_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_427_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_425l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_427_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_425l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_427_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_425l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_427 :
    hubcapFit theRedpart rf6 p6_425l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_427_1, c6_427_2, c6_427_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_429_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_424l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_429_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_424l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_429_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_424l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_429 :
    hubcapFit theRedpart rf6 p6_424l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_429_1, c6_429_2, c6_429_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_431_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_430r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_431_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_430r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_431_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_430r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_431 :
    hubcapFit theRedpart rf6 p6_430r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_431_1, c6_431_2, c6_431_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_432_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_430l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_432_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_430l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_432_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_430l) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_432 :
    hubcapFit theRedpart rf6 p6_430l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_432_1, c6_432_2, c6_432_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_440_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_439r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_440_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_439r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_440_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_439r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_440 :
    hubcapFit theRedpart rf6 p6_439r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_440_1, c6_440_2, c6_440_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_441_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_439l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_441_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_439l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_441_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_439l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_441 :
    hubcapFit theRedpart rf6 p6_439l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_441_1, c6_441_2, c6_441_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_443_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_438l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_443_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_438l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_443_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_438l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_443 :
    hubcapFit theRedpart rf6 p6_438l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_443_1, c6_443_2, c6_443_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_444_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_437l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_444_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_437l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_444_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_437l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_444 :
    hubcapFit theRedpart rf6 p6_437l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_444_1, c6_444_2, c6_444_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_447_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_446r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_447_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_446r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_447_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_446r) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_447 :
    hubcapFit theRedpart rf6 p6_446r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_447_1, c6_447_2, c6_447_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_448_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_446l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_448_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_446l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_448_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_446l) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_448 :
    hubcapFit theRedpart rf6 p6_446l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_448_1, c6_448_2, c6_448_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_452_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_451r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_452_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_451r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_452_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_451r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_452 :
    hubcapFit theRedpart rf6 p6_451r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_452_1, c6_452_2, c6_452_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_453_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_451l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_453_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_451l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_453_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_451l) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_453 :
    hubcapFit theRedpart rf6 p6_451l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_453_1, c6_453_2, c6_453_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_455_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_450l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_455_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_450l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_455_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_450l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_455 :
    hubcapFit theRedpart rf6 p6_450l
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_455_1, c6_455_2, c6_455_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_461_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_460r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_461_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_460r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_461_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_460r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_461 :
    hubcapFit theRedpart rf6 p6_460r
    (Hubcap.two 0 4 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_461_1, c6_461_2, c6_461_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_462_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_460l) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_462_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_460l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_462_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_460l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_462 :
    hubcapFit theRedpart rf6 p6_460l
    (Hubcap.two 0 4 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_462_1, c6_462_2, c6_462_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_465_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_464r) (hubSubn 6 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_465_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_464r) (hubSubn 6 2 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_465_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_464r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_465 :
    hubcapFit theRedpart rf6 p6_464r
    (Hubcap.two 0 4 2 <|
     Hubcap.two 1 2 (-2) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_465_1, c6_465_2, c6_465_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_466_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_464l) (hubSubn 6 4 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_466_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_464l) (hubSubn 6 2 1) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_466_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_464l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_466 :
    hubcapFit theRedpart rf6 p6_464l
    (Hubcap.two 0 4 1 <|
     Hubcap.two 1 2 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_466_1, c6_466_2, c6_466_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_468_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_458l) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_468_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_458l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_468_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_458l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_468 :
    hubcapFit theRedpart rf6 p6_458l
    (Hubcap.two 0 4 0 <|
     Hubcap.two 1 2 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_468_1, c6_468_2, c6_468_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_472_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_471r) (hubSubn 6 1 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_472_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_471r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_472_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_471r) (hubSubn 6 5 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_472 :
    hubcapFit theRedpart rf6 p6_471r
    (Hubcap.two 3 1 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 0 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_472_1, c6_472_2, c6_472_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_473_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_471l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_473_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_471l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_473_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_471l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_473 :
    hubcapFit theRedpart rf6 p6_471l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_473_1, c6_473_2, c6_473_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_475_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_470l) (hubSubn 6 1 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_475_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_470l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_475_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_470l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_475 :
    hubcapFit theRedpart rf6 p6_470l
    (Hubcap.two 0 1 (-2) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_475_1, c6_475_2, c6_475_3]

end FourColor

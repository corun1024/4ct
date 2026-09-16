import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 7 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_420_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_420_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_418l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_420_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_420_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_418l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_420_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_418l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_420 :
    hubcapFit theRedpart rf7 p7_418l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_420_1, c7_420_2, c7_420_3, c7_420_4, c7_420_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_417l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_417l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_422_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_417l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_422 :
    hubcapFit theRedpart rf7 p7_417l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_422_1, c7_422_2, c7_422_3, c7_422_4, c7_422_5, c7_422_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_424_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_415l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_424_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_424_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_424_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_415l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_424_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_415l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_424 :
    hubcapFit theRedpart rf7 p7_415l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_424_1, c7_424_2, c7_424_3, c7_424_4, c7_424_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_425_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_425_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_414l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_425_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_425_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_414l) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_425_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_414l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_425 :
    hubcapFit theRedpart rf7 p7_414l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_425_1, c7_425_2, c7_425_3, c7_425_4, c7_425_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_413l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_413l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_413l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_427_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_413l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_427 :
    hubcapFit theRedpart rf7 p7_413l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_427_1, c7_427_2, c7_427_3, c7_427_4, c7_427_5, c7_427_6, c7_427_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_431r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_431r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_431r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_431r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_431r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_432_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_431r) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_432 :
    hubcapFit theRedpart rf7 p7_431r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_432_1, c7_432_2, c7_432_3, c7_432_4, c7_432_5, c7_432_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_431l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_431l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_431l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_431l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_431l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_433_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_431l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_433 :
    hubcapFit theRedpart rf7 p7_431l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_433_1, c7_433_2, c7_433_3, c7_433_4, c7_433_5, c7_433_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_435_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_430l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_435_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_430l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_435_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_430l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_435_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_430l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_435_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_430l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_435 :
    hubcapFit theRedpart rf7 p7_430l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_435_1, c7_435_2, c7_435_3, c7_435_4, c7_435_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_437_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_410l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_437_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_410l) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_437_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_410l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_437_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_410l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_437 :
    hubcapFit theRedpart rf7 p7_410l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_437_1, c7_437_2, c7_437_3, c7_437_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_439_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_439_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_409l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_439_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_439_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_409l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_439_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_409l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_439 :
    hubcapFit theRedpart rf7 p7_409l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_439_1, c7_439_2, c7_439_3, c7_439_4, c7_439_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_458r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_458r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_458r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_458r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_458r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_459_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_458r) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_459 :
    hubcapFit theRedpart rf7 p7_458r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_459_1, c7_459_2, c7_459_3, c7_459_4, c7_459_5, c7_459_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_456l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_456l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_456l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_461_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_456l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_461 :
    hubcapFit theRedpart rf7 p7_456l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_461_1, c7_461_2, c7_461_3, c7_461_4, c7_461_5, c7_461_6, c7_461_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_463_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_455l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_463_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_455l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_463_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_455l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_463_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_455l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_463_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_455l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_463 :
    hubcapFit theRedpart rf7 p7_455l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_463_1, c7_463_2, c7_463_3, c7_463_4, c7_463_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_454l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_454l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_454l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_454l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_454l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_454l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_464_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_454l) (hubSubn 7 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_464 :
    hubcapFit theRedpart rf7 p7_454l
    (Hubcap.one 0 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_464_1, c7_464_2, c7_464_3, c7_464_4, c7_464_5, c7_464_6, c7_464_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_466_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_453l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_466_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_466_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_453l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_466_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_453l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_466_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_453l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_466 :
    hubcapFit theRedpart rf7 p7_453l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_466_1, c7_466_2, c7_466_3, c7_466_4, c7_466_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_467_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_467_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_467_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_467_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_452l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_467_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_452l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_467 :
    hubcapFit theRedpart rf7 p7_452l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_467_1, c7_467_2, c7_467_3, c7_467_4, c7_467_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_451l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_451l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_451l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_451l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_469_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_451l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_469 :
    hubcapFit theRedpart rf7 p7_451l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_469_1, c7_469_2, c7_469_3, c7_469_4, c7_469_5, c7_469_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_478r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_478r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_478r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_478r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_478r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_479_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_478r) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_479 :
    hubcapFit theRedpart rf7 p7_478r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_479_1, c7_479_2, c7_479_3, c7_479_4, c7_479_5, c7_479_6]

end FourColor

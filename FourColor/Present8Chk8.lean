import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 8 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_383l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_383l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_383l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_383l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_402_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_383l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_402 :
    hubcapFit theRedpart rf8 p8_383l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_402_1, c8_402_2, c8_402_3, c8_402_4, c8_402_5, c8_402_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_382l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_382l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_382l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_404_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_382l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_404 :
    hubcapFit theRedpart rf8 p8_382l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_404_1, c8_404_2, c8_404_3, c8_404_4, c8_404_5, c8_404_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_381l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_381l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_381l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_381l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_381l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_405_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_381l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_405 :
    hubcapFit theRedpart rf8 p8_381l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_405_1, c8_405_2, c8_405_3, c8_405_4, c8_405_5, c8_405_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_380l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_380l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_407_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_380l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_407 :
    hubcapFit theRedpart rf8 p8_380l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_407_1, c8_407_2, c8_407_3, c8_407_4, c8_407_5, c8_407_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_414_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_413r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_414_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_413r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_414_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_413r) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_414_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_413r) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_414_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_413r) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_414 :
    hubcapFit theRedpart rf8 p8_413r
    (Hubcap.one 3 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_414_1, c8_414_2, c8_414_3, c8_414_4, c8_414_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_413l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_413l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_415_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_413l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_415 :
    hubcapFit theRedpart rf8 p8_413l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_415_1, c8_415_2, c8_415_3, c8_415_4, c8_415_5, c8_415_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_412l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_412l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_412l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_417_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_412l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_417 :
    hubcapFit theRedpart rf8 p8_412l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_417_1, c8_417_2, c8_417_3, c8_417_4, c8_417_5, c8_417_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_411l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_411l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_411l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_411l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_418_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_411l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_418 :
    hubcapFit theRedpart rf8 p8_411l
    (Hubcap.one 7 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_418_1, c8_418_2, c8_418_3, c8_418_4, c8_418_5, c8_418_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_410l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_410l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_410l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_410l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_410l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_410l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_420_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_410l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_420 :
    hubcapFit theRedpart rf8 p8_410l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_420_1, c8_420_2, c8_420_3, c8_420_4, c8_420_5, c8_420_6, c8_420_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_422_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_422_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_409l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_422_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_409l) (hubSubn 8 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_422_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_409l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_422_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_409l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_422 :
    hubcapFit theRedpart rf8 p8_409l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_422_1, c8_422_2, c8_422_3, c8_422_4, c8_422_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_408l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_408l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_408l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_408l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_423_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_408l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_423 :
    hubcapFit theRedpart rf8 p8_408l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_423_1, c8_423_2, c8_423_3, c8_423_4, c8_423_5, c8_423_6, c8_423_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_426_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_426_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_426_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_378l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_426_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_378l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_426_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_378l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_426 :
    hubcapFit theRedpart rf8 p8_378l
    (Hubcap.one 3 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_426_1, c8_426_2, c8_426_3, c8_426_4, c8_426_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_428_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_428_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_376l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_428_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_376l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_428_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_376l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_428_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_376l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_428 :
    hubcapFit theRedpart rf8 p8_376l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_428_1, c8_428_2, c8_428_3, c8_428_4, c8_428_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_375l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_375l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_375l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_429_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_375l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_429 :
    hubcapFit theRedpart rf8 p8_375l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_429_1, c8_429_2, c8_429_3, c8_429_4, c8_429_5, c8_429_6, c8_429_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_374l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_431_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_374l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_431 :
    hubcapFit theRedpart rf8 p8_374l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_431_1, c8_431_2, c8_431_3, c8_431_4, c8_431_5, c8_431_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_432_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_432_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_432_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_373l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_432_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_373l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_432_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_373l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_432 :
    hubcapFit theRedpart rf8 p8_373l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_432_1, c8_432_2, c8_432_3, c8_432_4, c8_432_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_434_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_434_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_434_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_372l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_434_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_372l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_434_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_372l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_434 :
    hubcapFit theRedpart rf8 p8_372l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_434_1, c8_434_2, c8_434_3, c8_434_4, c8_434_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_436_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_436_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_436_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_307l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_436_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_307l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_436_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_307l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_436 :
    hubcapFit theRedpart rf8 p8_307l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_436_1, c8_436_2, c8_436_3, c8_436_4, c8_436_5]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 29 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1424l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1435_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1435 :
    hubcapFit theRedpart rf8 p8_1424l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1435_1, c8_1435_2, c8_1435_3, c8_1435_4, c8_1435_5, c8_1435_6, c8_1435_7, c8_1435_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1412l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1412l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1412l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1412l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1438_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1412l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1438 :
    hubcapFit theRedpart rf8 p8_1412l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1438_1, c8_1438_2, c8_1438_3, c8_1438_4, c8_1438_5, c8_1438_6, c8_1438_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1411l) (hubSubn 8 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1440_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1411l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1440 :
    hubcapFit theRedpart rf8 p8_1411l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1440_1, c8_1440_2, c8_1440_3, c8_1440_4, c8_1440_5, c8_1440_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1443_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1442r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1443_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1442r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1443_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1442r) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1443_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1442r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1443_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1442r) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1443 :
    hubcapFit theRedpart rf8 p8_1442r
    (Hubcap.one 1 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1443_1, c8_1443_2, c8_1443_3, c8_1443_4, c8_1443_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1442l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1442l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1444_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1444 :
    hubcapFit theRedpart rf8 p8_1442l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1444_1, c8_1444_2, c8_1444_3, c8_1444_4, c8_1444_5, c8_1444_6, c8_1444_7, c8_1444_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1447_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1409l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1447_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1409l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1447_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1409l) (hubSubn 8 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1447_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1409l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1447_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1409l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1447 :
    hubcapFit theRedpart rf8 p8_1409l
    (Hubcap.one 1 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1447_1, c8_1447_2, c8_1447_3, c8_1447_4, c8_1447_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1408l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1408l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1408l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1448_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1408l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1448 :
    hubcapFit theRedpart rf8 p8_1408l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1448_1, c8_1448_2, c8_1448_3, c8_1448_4, c8_1448_5, c8_1448_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1453r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1453r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1453r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1453r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1453r) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1454_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1453r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1454 :
    hubcapFit theRedpart rf8 p8_1453r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1454_1, c8_1454_2, c8_1454_3, c8_1454_4, c8_1454_5, c8_1454_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1453l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1453l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1453l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1455_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1453l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1455 :
    hubcapFit theRedpart rf8 p8_1453l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1455_1, c8_1455_2, c8_1455_3, c8_1455_4, c8_1455_5, c8_1455_6, c8_1455_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1452l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1452l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1457_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1457 :
    hubcapFit theRedpart rf8 p8_1452l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1457_1, c8_1457_2, c8_1457_3, c8_1457_4, c8_1457_5, c8_1457_6, c8_1457_7, c8_1457_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1451l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1451l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1451l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1451l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1451l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1459_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1451l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1459 :
    hubcapFit theRedpart rf8 p8_1451l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1459_1, c8_1459_2, c8_1459_3, c8_1459_4, c8_1459_5, c8_1459_6, c8_1459_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1470r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1470r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1470r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1470r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1470r) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1471_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1470r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1471 :
    hubcapFit theRedpart rf8 p8_1470r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1471_1, c8_1471_2, c8_1471_3, c8_1471_4, c8_1471_5, c8_1471_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1472_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1470l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1472_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1470l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1472_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1470l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1472_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1470l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1472_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1470l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1472 :
    hubcapFit theRedpart rf8 p8_1470l
    (Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1472_1, c8_1472_2, c8_1472_3, c8_1472_4, c8_1472_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1469l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1469l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1469l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1469l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1469l) (hubSubn 8 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1474_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1469l) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1474 :
    hubcapFit theRedpart rf8 p8_1469l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1474_1, c8_1474_2, c8_1474_3, c8_1474_4, c8_1474_5, c8_1474_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1477r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1477r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1477r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1477r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1478_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1477r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1478 :
    hubcapFit theRedpart rf8 p8_1477r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1478_1, c8_1478_2, c8_1478_3, c8_1478_4, c8_1478_5, c8_1478_6, c8_1478_7, c8_1478_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1477l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1477l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1479_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1477l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1479 :
    hubcapFit theRedpart rf8 p8_1477l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1479_1, c8_1479_2, c8_1479_3, c8_1479_4, c8_1479_5, c8_1479_6]

end FourColor

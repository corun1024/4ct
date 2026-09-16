import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 30 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1475l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1475l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1481_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1481 :
    hubcapFit theRedpart rf8 p8_1475l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1481_1, c8_1481_2, c8_1481_3, c8_1481_4, c8_1481_5, c8_1481_6, c8_1481_7, c8_1481_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1467l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1467l) (hubSubn 8 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1467l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1467l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1467l) (hubSubn 8 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1484_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1467l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1484 :
    hubcapFit theRedpart rf8 p8_1467l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1484_1, c8_1484_2, c8_1484_3, c8_1484_4, c8_1484_5, c8_1484_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1485_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1466l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1485_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1466l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1485_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1466l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1485_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1466l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1485_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1466l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1485 :
    hubcapFit theRedpart rf8 p8_1466l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1485_1, c8_1485_2, c8_1485_3, c8_1485_4, c8_1485_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1491r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1491r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1491r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1491r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1491r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1491r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1492_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1492 :
    hubcapFit theRedpart rf8 p8_1491r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1492_1, c8_1492_2, c8_1492_3, c8_1492_4, c8_1492_5, c8_1492_6, c8_1492_7, c8_1492_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1491l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1491l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1491l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1493_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1491l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1493 :
    hubcapFit theRedpart rf8 p8_1491l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1493_1, c8_1493_2, c8_1493_3, c8_1493_4, c8_1493_5, c8_1493_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1490l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1490l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1495_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1490l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1495 :
    hubcapFit theRedpart rf8 p8_1490l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1495_1, c8_1495_2, c8_1495_3, c8_1495_4, c8_1495_5, c8_1495_6, c8_1495_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1489l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1497_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1489l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1497 :
    hubcapFit theRedpart rf8 p8_1489l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1497_1, c8_1497_2, c8_1497_3, c8_1497_4, c8_1497_5, c8_1497_6, c8_1497_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1488l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1488l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1499_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1488l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1499 :
    hubcapFit theRedpart rf8 p8_1488l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1499_1, c8_1499_2, c8_1499_3, c8_1499_4, c8_1499_5, c8_1499_6, c8_1499_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1487l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1487l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1487l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1501_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1501 :
    hubcapFit theRedpart rf8 p8_1487l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1501_1, c8_1501_2, c8_1501_3, c8_1501_4, c8_1501_5, c8_1501_6, c8_1501_7, c8_1501_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1506r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1506r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1506r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1506r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1506r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1507_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1506r) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1507 :
    hubcapFit theRedpart rf8 p8_1506r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1507_1, c8_1507_2, c8_1507_3, c8_1507_4, c8_1507_5, c8_1507_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1506l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1506l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1506l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1506l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1506l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1508_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1506l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1508 :
    hubcapFit theRedpart rf8 p8_1506l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1508_1, c8_1508_2, c8_1508_3, c8_1508_4, c8_1508_5, c8_1508_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1505l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1505l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1505l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1505l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1510_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1505l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1510 :
    hubcapFit theRedpart rf8 p8_1505l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1510_1, c8_1510_2, c8_1510_3, c8_1510_4, c8_1510_5, c8_1510_6, c8_1510_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1504l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1504l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1512_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1504l) (hubSubn 8 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1512 :
    hubcapFit theRedpart rf8 p8_1504l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1512_1, c8_1512_2, c8_1512_3, c8_1512_4, c8_1512_5, c8_1512_6, c8_1512_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1522r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1522r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1522r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1522r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1522r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1522r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1522r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1523_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1522r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1523 :
    hubcapFit theRedpart rf8 p8_1522r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1523_1, c8_1523_2, c8_1523_3, c8_1523_4, c8_1523_5, c8_1523_6, c8_1523_7, c8_1523_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1522l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1522l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1522l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1524_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1522l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1524 :
    hubcapFit theRedpart rf8 p8_1522l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1524_1, c8_1524_2, c8_1524_3, c8_1524_4, c8_1524_5, c8_1524_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1521l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1521l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1521l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1521l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1521l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1521l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1526_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1521l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1526 :
    hubcapFit theRedpart rf8 p8_1521l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1526_1, c8_1526_2, c8_1526_3, c8_1526_4, c8_1526_5, c8_1526_6, c8_1526_7]

end FourColor

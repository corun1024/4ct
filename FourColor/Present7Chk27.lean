import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 27 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1482_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1477l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1482_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1477l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1482_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1477l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1482_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1477l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1482 :
    hubcapFit theRedpart rf7 p7_1477l
    (Hubcap.one 1 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1482_1, c7_1482_2, c7_1482_3, c7_1482_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1485r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1485r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1485r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1485r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1485r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1486_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1485r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1486 :
    hubcapFit theRedpart rf7 p7_1485r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1486_1, c7_1486_2, c7_1486_3, c7_1486_4, c7_1486_5, c7_1486_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1485l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1485l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1485l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1485l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1485l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1487_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1485l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1487 :
    hubcapFit theRedpart rf7 p7_1485l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1487_1, c7_1487_2, c7_1487_3, c7_1487_4, c7_1487_5, c7_1487_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1489_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1489_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1484l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1489_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1484l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1489_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1484l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1489_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1484l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1489 :
    hubcapFit theRedpart rf7 p7_1484l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1489_1, c7_1489_2, c7_1489_3, c7_1489_4, c7_1489_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1495r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1495r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1495r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1495r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1495r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1495r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1496_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1495r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1496 :
    hubcapFit theRedpart rf7 p7_1495r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1496_1, c7_1496_2, c7_1496_3, c7_1496_4, c7_1496_5, c7_1496_6, c7_1496_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1495l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1495l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1495l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1497_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1495l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1497 :
    hubcapFit theRedpart rf7 p7_1495l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1497_1, c7_1497_2, c7_1497_3, c7_1497_4, c7_1497_5, c7_1497_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1502_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1501r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1502_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1501r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1502_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1501r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1502_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1501r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1502_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1501r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1502 :
    hubcapFit theRedpart rf7 p7_1501r
    (Hubcap.one 0 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1502_1, c7_1502_2, c7_1502_3, c7_1502_4, c7_1502_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1501l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1501l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1501l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1503_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1501l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1503 :
    hubcapFit theRedpart rf7 p7_1501l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1503_1, c7_1503_2, c7_1503_3, c7_1503_4, c7_1503_5, c7_1503_6, c7_1503_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1499l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1499l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1499l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1499l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1505_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1499l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1505 :
    hubcapFit theRedpart rf7 p7_1499l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1505_1, c7_1505_2, c7_1505_3, c7_1505_4, c7_1505_5, c7_1505_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1509r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1509r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1509r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1509r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1509r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1509r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1510_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1509r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1510 :
    hubcapFit theRedpart rf7 p7_1509r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1510_1, c7_1510_2, c7_1510_3, c7_1510_4, c7_1510_5, c7_1510_6, c7_1510_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1511_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1511_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1511_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1509l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1511_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1509l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1511_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1509l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1511 :
    hubcapFit theRedpart rf7 p7_1509l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1511_1, c7_1511_2, c7_1511_3, c7_1511_4, c7_1511_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1513_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1513_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1513_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1513_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1508l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1513_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1508l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1513 :
    hubcapFit theRedpart rf7 p7_1508l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1513_1, c7_1513_2, c7_1513_3, c7_1513_4, c7_1513_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1514_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1507l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1514_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1507l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1514_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1507l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1514_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1507l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1514_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1507l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1514 :
    hubcapFit theRedpart rf7 p7_1507l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1514_1, c7_1514_2, c7_1514_3, c7_1514_4, c7_1514_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1524r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1524r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1524r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1524r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1524r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1525_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1524r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1525 :
    hubcapFit theRedpart rf7 p7_1524r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1525_1, c7_1525_2, c7_1525_3, c7_1525_4, c7_1525_5, c7_1525_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1526_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1526_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1526_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1524l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1526_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1524l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1526_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1524l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1526 :
    hubcapFit theRedpart rf7 p7_1524l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1526_1, c7_1526_2, c7_1526_3, c7_1526_4, c7_1526_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1529_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1528r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1529_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1528r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1529_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1528r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1529_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1528r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1529_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1528r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1529 :
    hubcapFit theRedpart rf7 p7_1528r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1529_1, c7_1529_2, c7_1529_3, c7_1529_4, c7_1529_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1528l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1528l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1528l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1528l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1530_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1528l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1530 :
    hubcapFit theRedpart rf7 p7_1528l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1530_1, c7_1530_2, c7_1530_3, c7_1530_4, c7_1530_5, c7_1530_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1532_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1522l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1532_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1522l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1532_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1522l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1532_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1522l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1532_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1522l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1532 :
    hubcapFit theRedpart rf7 p7_1522l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1532_1, c7_1532_2, c7_1532_3, c7_1532_4, c7_1532_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1534_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1521l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1534_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1521l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1534_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1521l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1534_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1521l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1534 :
    hubcapFit theRedpart rf7 p7_1521l
    (Hubcap.one 1 2 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1534_1, c7_1534_2, c7_1534_3, c7_1534_4]

end FourColor

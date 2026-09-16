import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 26 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1433l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1433l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1433l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1433l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1433l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1433l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1435_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1433l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1435 :
    hubcapFit theRedpart rf7 p7_1433l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1435_1, c7_1435_2, c7_1435_3, c7_1435_4, c7_1435_5, c7_1435_6, c7_1435_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1437_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1432l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1437_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1432l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1437_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1432l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1437_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1432l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1437_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1432l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1437 :
    hubcapFit theRedpart rf7 p7_1432l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1437_1, c7_1437_2, c7_1437_3, c7_1437_4, c7_1437_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1440_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1439r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1440_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1439r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1440_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1439r) (hubSubn 7 4 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1440_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1439r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1440 :
    hubcapFit theRedpart rf7 p7_1439r
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1440_1, c7_1440_2, c7_1440_3, c7_1440_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1439l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1439l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1439l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1439l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1439l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1441_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1439l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1441 :
    hubcapFit theRedpart rf7 p7_1439l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1441_1, c7_1441_2, c7_1441_3, c7_1441_4, c7_1441_5, c7_1441_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1429l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1429l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1429l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1429l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1443_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1429l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1443 :
    hubcapFit theRedpart rf7 p7_1429l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1443_1, c7_1443_2, c7_1443_3, c7_1443_4, c7_1443_5, c7_1443_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1449_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1448r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1449_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1448r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1449_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1448r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1449_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1448r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1449_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1448r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1449 :
    hubcapFit theRedpart rf7 p7_1448r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1449_1, c7_1449_2, c7_1449_3, c7_1449_4, c7_1449_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1448l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1448l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1450_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1448l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1450 :
    hubcapFit theRedpart rf7 p7_1448l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1450_1, c7_1450_2, c7_1450_3, c7_1450_4, c7_1450_5, c7_1450_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1452_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1452_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1447l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1452_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1447l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1452_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1447l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1452_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1447l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1452 :
    hubcapFit theRedpart rf7 p7_1447l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1452_1, c7_1452_2, c7_1452_3, c7_1452_4, c7_1452_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1453_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1453_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1453_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1453_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1446l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1453_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1446l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1453 :
    hubcapFit theRedpart rf7 p7_1446l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1453_1, c7_1453_2, c7_1453_3, c7_1453_4, c7_1453_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1455_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1455_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1455_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1445l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1455_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1445l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1455_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1445l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1455 :
    hubcapFit theRedpart rf7 p7_1445l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1455_1, c7_1455_2, c7_1455_3, c7_1455_4, c7_1455_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1465r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1465r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1465r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1465r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1465r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1465r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1466_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1465r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1466 :
    hubcapFit theRedpart rf7 p7_1465r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1466_1, c7_1466_2, c7_1466_3, c7_1466_4, c7_1466_5, c7_1466_6, c7_1466_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1465l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1465l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1465l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1467_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1467 :
    hubcapFit theRedpart rf7 p7_1465l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1467_1, c7_1467_2, c7_1467_3, c7_1467_4, c7_1467_5, c7_1467_6, c7_1467_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1469_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1464l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1469_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1464l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1469_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1464l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1469_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1464l) (hubSubn 7 5 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1469_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1464l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1469 :
    hubcapFit theRedpart rf7 p7_1464l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 5 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1469_1, c7_1469_2, c7_1469_3, c7_1469_4, c7_1469_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1462l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1462l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1471_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1462l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1471 :
    hubcapFit theRedpart rf7 p7_1462l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1471_1, c7_1471_2, c7_1471_3, c7_1471_4, c7_1471_5, c7_1471_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1461l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1461l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1461l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1461l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1472_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1461l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1472 :
    hubcapFit theRedpart rf7 p7_1461l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1472_1, c7_1472_2, c7_1472_3, c7_1472_4, c7_1472_5, c7_1472_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1474_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1460l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1474_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1460l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1474_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1460l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1474_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1460l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1474_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1460l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1474 :
    hubcapFit theRedpart rf7 p7_1460l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1474_1, c7_1474_2, c7_1474_3, c7_1474_4, c7_1474_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1459l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1459l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1459l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1459l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1475_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1459l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1475 :
    hubcapFit theRedpart rf7 p7_1459l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1475_1, c7_1475_2, c7_1475_3, c7_1475_4, c7_1475_5, c7_1475_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1479_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1478r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1479_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1478r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1479_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1478r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1479_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1478r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1479 :
    hubcapFit theRedpart rf7 p7_1478r
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1479_1, c7_1479_2, c7_1479_3, c7_1479_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1480_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1478l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1480_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1478l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1480_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1478l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1480_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1478l) (hubSubn 7 5 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1480_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1478l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1480 :
    hubcapFit theRedpart rf7 p7_1478l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 5 2 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1480_1, c7_1480_2, c7_1480_3, c7_1480_4, c7_1480_5]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 30 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1407l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1407l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1407l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1407l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1407l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1407l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1407l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1407l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1415_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1407l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1415 :
    hubcapFit theRedpart rf9 p9_1407l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1415_1, c9_1415_2, c9_1415_3, c9_1415_4, c9_1415_5, c9_1415_6, c9_1415_7, c9_1415_8, c9_1415_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1398l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1398l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1398l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1398l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1398l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1417_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1398l) (hubSubn 9 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1417 :
    hubcapFit theRedpart rf9 p9_1398l
    (Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1417_1, c9_1417_2, c9_1417_3, c9_1417_4, c9_1417_5, c9_1417_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1396l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1396l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1396l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1396l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1396l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1419_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1396l) (hubSubn 9 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1419 :
    hubcapFit theRedpart rf9 p9_1396l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1419_1, c9_1419_2, c9_1419_3, c9_1419_4, c9_1419_5, c9_1419_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1395l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1395l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1395l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1421_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1395l) (hubSubn 9 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1421 :
    hubcapFit theRedpart rf9 p9_1395l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1421_1, c9_1421_2, c9_1421_3, c9_1421_4, c9_1421_5, c9_1421_6, c9_1421_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1394l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1394l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1394l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1394l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1394l) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1423_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1394l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1423 :
    hubcapFit theRedpart rf9 p9_1394l
    (Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1423_1, c9_1423_2, c9_1423_3, c9_1423_4, c9_1423_5, c9_1423_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1424_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1393l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1424 :
    hubcapFit theRedpart rf9 p9_1393l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1424_1, c9_1424_2, c9_1424_3, c9_1424_4, c9_1424_5, c9_1424_6, c9_1424_7, c9_1424_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1392l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1392l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1392l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1426_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1392l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1426 :
    hubcapFit theRedpart rf9 p9_1392l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1426_1, c9_1426_2, c9_1426_3, c9_1426_4, c9_1426_5, c9_1426_6, c9_1426_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1428l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1428l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1428l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1428l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1429_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1428l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1429 :
    hubcapFit theRedpart rf9 p9_1428l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1429_1, c9_1429_2, c9_1429_3, c9_1429_4, c9_1429_5, c9_1429_6, c9_1429_7, c9_1429_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1428r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1428r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1431_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1428r) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1431 :
    hubcapFit theRedpart rf9 p9_1428r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1431_1, c9_1431_2, c9_1431_3, c9_1431_4, c9_1431_5, c9_1431_6, c9_1431_7, c9_1431_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1321l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1321l) (hubSubn 9 4 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1321l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1434_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1321l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1434 :
    hubcapFit theRedpart rf9 p9_1321l
    (Hubcap.one 0 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 7 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1434_1, c9_1434_2, c9_1434_3, c9_1434_4, c9_1434_5, c9_1434_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1320l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1320l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1320l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1320l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1320l) (hubSubn 9 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1320l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1436_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1320l) (hubSubn 9 4 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1436 :
    hubcapFit theRedpart rf9 p9_1320l
    (Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 3 4 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1436_1, c9_1436_2, c9_1436_3, c9_1436_4, c9_1436_5, c9_1436_6, c9_1436_7, c9_1436_8, c9_1436_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1453r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1453r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1453r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1453r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1453r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1453r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1453r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1454_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1453r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1454 :
    hubcapFit theRedpart rf9 p9_1453r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1454_1, c9_1454_2, c9_1454_3, c9_1454_4, c9_1454_5, c9_1454_6, c9_1454_7, c9_1454_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1453l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1455_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1453l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1455 :
    hubcapFit theRedpart rf9 p9_1453l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1455_1, c9_1455_2, c9_1455_3, c9_1455_4, c9_1455_5, c9_1455_6, c9_1455_7, c9_1455_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1451l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1451l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1451l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1451l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1451l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1457_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1451l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1457 :
    hubcapFit theRedpart rf9 p9_1451l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1457_1, c9_1457_2, c9_1457_3, c9_1457_4, c9_1457_5, c9_1457_6, c9_1457_7, c9_1457_8, c9_1457_9]

end FourColor

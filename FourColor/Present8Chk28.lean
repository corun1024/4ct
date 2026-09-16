import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 28 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1382l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1382l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1382l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1382l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1389_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1382l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1389 :
    hubcapFit theRedpart rf8 p8_1382l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1389_1, c8_1389_2, c8_1389_3, c8_1389_4, c8_1389_5, c8_1389_6, c8_1389_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1381l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1381l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1381l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1381l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1381l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1391_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1381l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1391 :
    hubcapFit theRedpart rf8 p8_1381l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1391_1, c8_1391_2, c8_1391_3, c8_1391_4, c8_1391_5, c8_1391_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1380l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1380l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1380l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1380l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1392_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1380l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1392 :
    hubcapFit theRedpart rf8 p8_1380l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1392_1, c8_1392_2, c8_1392_3, c8_1392_4, c8_1392_5, c8_1392_6, c8_1392_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1396_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1396_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1396_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1395r) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1396_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1395r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1396_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1395r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1396 :
    hubcapFit theRedpart rf8 p8_1395r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1396_1, c8_1396_2, c8_1396_3, c8_1396_4, c8_1396_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1395l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1395l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1395l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1395l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1397_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1395l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1397 :
    hubcapFit theRedpart rf8 p8_1395l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1397_1, c8_1397_2, c8_1397_3, c8_1397_4, c8_1397_5, c8_1397_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1403_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1402r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1403_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1402r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1403_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1402r) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1403_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1402r) (hubSubn 8 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1403_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1402r) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1403 :
    hubcapFit theRedpart rf8 p8_1402r
    (Hubcap.one 0 2 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1403_1, c8_1403_2, c8_1403_3, c8_1403_4, c8_1403_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1402l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1402l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1402l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1402l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1402l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1404_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1402l) (hubSubn 8 7 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1404 :
    hubcapFit theRedpart rf8 p8_1402l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1404_1, c8_1404_2, c8_1404_3, c8_1404_4, c8_1404_5, c8_1404_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1401l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1401l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1401l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1401l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1401l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1406_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1401l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1406 :
    hubcapFit theRedpart rf8 p8_1401l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1406_1, c8_1406_2, c8_1406_3, c8_1406_4, c8_1406_5, c8_1406_6, c8_1406_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1416r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1416r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1416r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1416r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1416r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1416r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1416r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1417_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1416r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1417 :
    hubcapFit theRedpart rf8 p8_1416r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1417_1, c8_1417_2, c8_1417_3, c8_1417_4, c8_1417_5, c8_1417_6, c8_1417_7, c8_1417_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1418_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1416l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1418_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1416l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1418_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1416l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1418_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1416l) (hubSubn 8 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1418_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1416l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1418 :
    hubcapFit theRedpart rf8 p8_1416l
    (Hubcap.one 1 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1418_1, c8_1418_2, c8_1418_3, c8_1418_4, c8_1418_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1415l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1415l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1415l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1415l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1420_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1415l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1420 :
    hubcapFit theRedpart rf8 p8_1415l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1420_1, c8_1420_2, c8_1420_3, c8_1420_4, c8_1420_5, c8_1420_6, c8_1420_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1414l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1414l) (hubSubn 8 6 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1422_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1414l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1422 :
    hubcapFit theRedpart rf8 p8_1414l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 6 8 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1422_1, c8_1422_2, c8_1422_3, c8_1422_4, c8_1422_5, c8_1422_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1427r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1427r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1427r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1427r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1427r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1427r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1428_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1427r) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1428 :
    hubcapFit theRedpart rf8 p8_1427r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1428_1, c8_1428_2, c8_1428_3, c8_1428_4, c8_1428_5, c8_1428_6, c8_1428_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1427l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1427l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1427l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1427l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1427l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1429_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1429 :
    hubcapFit theRedpart rf8 p8_1427l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1429_1, c8_1429_2, c8_1429_3, c8_1429_4, c8_1429_5, c8_1429_6, c8_1429_7, c8_1429_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1426l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1426l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1426l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1426l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1431_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1431 :
    hubcapFit theRedpart rf8 p8_1426l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1431_1, c8_1431_2, c8_1431_3, c8_1431_4, c8_1431_5, c8_1431_6, c8_1431_7, c8_1431_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1425l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1425l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1433_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1433 :
    hubcapFit theRedpart rf8 p8_1425l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1433_1, c8_1433_2, c8_1433_3, c8_1433_4, c8_1433_5, c8_1433_6, c8_1433_7, c8_1433_8]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 32 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1486l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1486l) (hubSubn 9 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1486l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1486l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1486l) (hubSubn 9 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1500_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1486l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1500 :
    hubcapFit theRedpart rf9 p9_1486l
    (Hubcap.one 0 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1500_1, c9_1500_2, c9_1500_3, c9_1500_4, c9_1500_5, c9_1500_6, c9_1500_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1484l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1484l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1484l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1484l) (hubSubn 9 7 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1502_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1484l) (hubSubn 9 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1502 :
    hubcapFit theRedpart rf9 p9_1484l
    (Hubcap.one 0 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 1 7 6 <|
     Hubcap.two 4 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1502_1, c9_1502_2, c9_1502_3, c9_1502_4, c9_1502_5, c9_1502_6, c9_1502_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1483l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1483l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1483l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1483l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1504_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1483l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1504 :
    hubcapFit theRedpart rf9 p9_1483l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1504_1, c9_1504_2, c9_1504_3, c9_1504_4, c9_1504_5, c9_1504_6, c9_1504_7, c9_1504_8, c9_1504_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1482l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1482l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1482l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1482l) (hubSubn 9 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1482l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1506_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1482l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1506 :
    hubcapFit theRedpart rf9 p9_1482l
    (Hubcap.one 0 5 <|
     Hubcap.one 4 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1506_1, c9_1506_2, c9_1506_3, c9_1506_4, c9_1506_5, c9_1506_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1481l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1481l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1481l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1481l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1481l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1481l) (hubSubn 9 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1507_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1481l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1507 :
    hubcapFit theRedpart rf9 p9_1481l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1507_1, c9_1507_2, c9_1507_3, c9_1507_4, c9_1507_5, c9_1507_6, c9_1507_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1439l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1439l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1439l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1439l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1439l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1439l) (hubSubn 9 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1509_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1439l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1509 :
    hubcapFit theRedpart rf9 p9_1439l
    (Hubcap.one 0 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1509_1, c9_1509_2, c9_1509_3, c9_1509_4, c9_1509_5, c9_1509_6, c9_1509_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1438l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1438l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1438l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1438l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1438l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1438l) (hubSubn 9 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1511_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1438l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1511 :
    hubcapFit theRedpart rf9 p9_1438l
    (Hubcap.one 0 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1511_1, c9_1511_2, c9_1511_3, c9_1511_4, c9_1511_5, c9_1511_6, c9_1511_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1316l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1316l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1316l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1316l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1513_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1316l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1513 :
    hubcapFit theRedpart rf9 p9_1316l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1513_1, c9_1513_2, c9_1513_3, c9_1513_4, c9_1513_5, c9_1513_6, c9_1513_7, c9_1513_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1315l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1515_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1315l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1515 :
    hubcapFit theRedpart rf9 p9_1315l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1515_1, c9_1515_2, c9_1515_3, c9_1515_4, c9_1515_5, c9_1515_6, c9_1515_7, c9_1515_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1314l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1314l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1314l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1314l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1314l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1517_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1314l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1517 :
    hubcapFit theRedpart rf9 p9_1314l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1517_1, c9_1517_2, c9_1517_3, c9_1517_4, c9_1517_5, c9_1517_6, c9_1517_7, c9_1517_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1519l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1519l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1519l) (hubSubn 9 2 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1520_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1519l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1520 :
    hubcapFit theRedpart rf9 p9_1519l
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1520_1, c9_1520_2, c9_1520_3, c9_1520_4, c9_1520_5, c9_1520_6, c9_1520_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1522l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1522l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1522l) (hubSubn 9 2 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1523_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1522l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1523 :
    hubcapFit theRedpart rf9 p9_1522l
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1523_1, c9_1523_2, c9_1523_3, c9_1523_4, c9_1523_5, c9_1523_6, c9_1523_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1526l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1526l) (hubSubn 9 2 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1527_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1526l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1527 :
    hubcapFit theRedpart rf9 p9_1526l
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1527_1, c9_1527_2, c9_1527_3, c9_1527_4, c9_1527_5, c9_1527_6, c9_1527_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1526r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1526r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1526r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1526r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1526r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1526r) (hubSubn 9 2 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1529_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1526r) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1529 :
    hubcapFit theRedpart rf9 p9_1526r
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1529_1, c9_1529_2, c9_1529_3, c9_1529_4, c9_1529_5, c9_1529_6, c9_1529_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1525r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1525r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1525r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1525r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1525r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1525r) (hubSubn 9 2 0) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1532_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1525r) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1532 :
    hubcapFit theRedpart rf9 p9_1525r
    (Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 9 <|
     Hubcap.two 1 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1532_1, c9_1532_2, c9_1532_3, c9_1532_4, c9_1532_5, c9_1532_6, c9_1532_7]

end FourColor

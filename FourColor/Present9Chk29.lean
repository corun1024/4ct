import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 29 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1328l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1328l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1328l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1328l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1374_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1328l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1374 :
    hubcapFit theRedpart rf9 p9_1328l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1374_1, c9_1374_2, c9_1374_3, c9_1374_4, c9_1374_5, c9_1374_6, c9_1374_7, c9_1374_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1327l) (hubSubn 9 4 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1327l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1327l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1327l) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1376_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1327l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1376 :
    hubcapFit theRedpart rf9 p9_1327l
    (Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 4 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 0 3 8 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1376_1, c9_1376_2, c9_1376_3, c9_1376_4, c9_1376_5, c9_1376_6, c9_1376_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1379r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1379r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1379r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1379r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1379r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1379r) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1380_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1379r) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1380 :
    hubcapFit theRedpart rf9 p9_1379r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1380_1, c9_1380_2, c9_1380_3, c9_1380_4, c9_1380_5, c9_1380_6, c9_1380_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1379l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1379l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1379l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1379l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1379l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1381_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1379l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1381 :
    hubcapFit theRedpart rf9 p9_1379l
    (Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1381_1, c9_1381_2, c9_1381_3, c9_1381_4, c9_1381_5, c9_1381_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1378l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1383_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1378l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1383 :
    hubcapFit theRedpart rf9 p9_1378l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1383_1, c9_1383_2, c9_1383_3, c9_1383_4, c9_1383_5, c9_1383_6, c9_1383_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1325l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1385_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1325l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1385 :
    hubcapFit theRedpart rf9 p9_1325l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1385_1, c9_1385_2, c9_1385_3, c9_1385_4, c9_1385_5, c9_1385_6, c9_1385_7, c9_1385_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1324l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1324l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1324l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1324l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1387_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1324l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1387 :
    hubcapFit theRedpart rf9 p9_1324l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1387_1, c9_1387_2, c9_1387_3, c9_1387_4, c9_1387_5, c9_1387_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1323l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1388_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1323l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1388 :
    hubcapFit theRedpart rf9 p9_1323l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1388_1, c9_1388_2, c9_1388_3, c9_1388_4, c9_1388_5, c9_1388_6, c9_1388_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1401r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1401r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1401r) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1401r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1401r) (hubSubn 9 4 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1401r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1402_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1401r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1402 :
    hubcapFit theRedpart rf9 p9_1401r
    (Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 0 2 8 <|
     Hubcap.two 1 4 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1402_1, c9_1402_2, c9_1402_3, c9_1402_4, c9_1402_5, c9_1402_6, c9_1402_7, c9_1402_8, c9_1402_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1401l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1401l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1401l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1403_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1401l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1403 :
    hubcapFit theRedpart rf9 p9_1401l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1403_1, c9_1403_2, c9_1403_3, c9_1403_4, c9_1403_5, c9_1403_6, c9_1403_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1400l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1400l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1400l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1400l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1400l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1400l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1400l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1400l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1405_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1400l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1405 :
    hubcapFit theRedpart rf9 p9_1400l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1405_1, c9_1405_2, c9_1405_3, c9_1405_4, c9_1405_5, c9_1405_6, c9_1405_7, c9_1405_8, c9_1405_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1409r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1409r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1409r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1409r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1409r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1409r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1409r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1410_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1409r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1410 :
    hubcapFit theRedpart rf9 p9_1409r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1410_1, c9_1410_2, c9_1410_3, c9_1410_4, c9_1410_5, c9_1410_6, c9_1410_7, c9_1410_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1409l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1409l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1409l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1409l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1411_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1411 :
    hubcapFit theRedpart rf9 p9_1409l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1411_1, c9_1411_2, c9_1411_3, c9_1411_4, c9_1411_5, c9_1411_6, c9_1411_7, c9_1411_8, c9_1411_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1408l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1408l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1408l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1408l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1408l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1413_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1408l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1413 :
    hubcapFit theRedpart rf9 p9_1408l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1413_1, c9_1413_2, c9_1413_3, c9_1413_4, c9_1413_5, c9_1413_6, c9_1413_7, c9_1413_8]

end FourColor

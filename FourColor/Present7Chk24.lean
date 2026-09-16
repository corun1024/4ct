import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 24 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1296l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1296l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1296l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1296l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1296l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1323_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1296l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1323 :
    hubcapFit theRedpart rf7 p7_1296l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1323_1, c7_1323_2, c7_1323_3, c7_1323_4, c7_1323_5, c7_1323_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1295l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1295l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1295l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1295l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1295l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1325_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1295l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1325 :
    hubcapFit theRedpart rf7 p7_1295l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1325_1, c7_1325_2, c7_1325_3, c7_1325_4, c7_1325_5, c7_1325_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1327_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1289l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1327_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1289l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1327_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1289l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1327_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1289l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1327_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1289l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1327 :
    hubcapFit theRedpart rf7 p7_1289l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1327_1, c7_1327_2, c7_1327_3, c7_1327_4, c7_1327_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1340r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1340r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1340r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1340r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1340r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1341_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1340r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1341 :
    hubcapFit theRedpart rf7 p7_1340r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1341_1, c7_1341_2, c7_1341_3, c7_1341_4, c7_1341_5, c7_1341_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1338l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1338l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1338l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1338l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1338l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1343_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1338l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1343 :
    hubcapFit theRedpart rf7 p7_1338l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1343_1, c7_1343_2, c7_1343_3, c7_1343_4, c7_1343_5, c7_1343_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1345_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1336l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1345_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1336l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1345_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1336l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1345_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1336l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1345_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1336l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1345 :
    hubcapFit theRedpart rf7 p7_1336l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1345_1, c7_1345_2, c7_1345_3, c7_1345_4, c7_1345_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1335l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1335l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1346_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1335l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1346 :
    hubcapFit theRedpart rf7 p7_1335l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1346_1, c7_1346_2, c7_1346_3, c7_1346_4, c7_1346_5, c7_1346_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1351r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1351r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1351r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1351r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1351r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1352_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1351r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1352 :
    hubcapFit theRedpart rf7 p7_1351r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1352_1, c7_1352_2, c7_1352_3, c7_1352_4, c7_1352_5, c7_1352_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1351l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1351l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1351l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1353_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1351l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1353 :
    hubcapFit theRedpart rf7 p7_1351l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1353_1, c7_1353_2, c7_1353_3, c7_1353_4, c7_1353_5, c7_1353_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1355_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1355_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1355_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1350l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1355_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1350l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1355_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1350l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1355 :
    hubcapFit theRedpart rf7 p7_1350l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1355_1, c7_1355_2, c7_1355_3, c7_1355_4, c7_1355_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1349l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1349l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1356_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1349l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1356 :
    hubcapFit theRedpart rf7 p7_1349l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1356_1, c7_1356_2, c7_1356_3, c7_1356_4, c7_1356_5, c7_1356_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1348l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1348l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1348l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1358_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1348l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1358 :
    hubcapFit theRedpart rf7 p7_1348l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1358_1, c7_1358_2, c7_1358_3, c7_1358_4, c7_1358_5, c7_1358_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1365r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1365r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1365r) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1365r) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1365r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1366_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1365r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1366 :
    hubcapFit theRedpart rf7 p7_1365r
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1366_1, c7_1366_2, c7_1366_3, c7_1366_4, c7_1366_5, c7_1366_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1367_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1365l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1367_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1365l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1367_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1365l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1367_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1365l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1367_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1365l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1367 :
    hubcapFit theRedpart rf7 p7_1365l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1367_1, c7_1367_2, c7_1367_3, c7_1367_4, c7_1367_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1369_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1364l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1369_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1364l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1369_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1364l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1369_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1364l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1369 :
    hubcapFit theRedpart rf7 p7_1364l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1369_1, c7_1369_2, c7_1369_3, c7_1369_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1374r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1374r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1374r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1374r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1374r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1374r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1375_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1374r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1375 :
    hubcapFit theRedpart rf7 p7_1374r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1375_1, c7_1375_2, c7_1375_3, c7_1375_4, c7_1375_5, c7_1375_6, c7_1375_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1374l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1374l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1374l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1376_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1374l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1376 :
    hubcapFit theRedpart rf7 p7_1374l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1376_1, c7_1376_2, c7_1376_3, c7_1376_4, c7_1376_5, c7_1376_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1373l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1373l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1373l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1378_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1373l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1378 :
    hubcapFit theRedpart rf7 p7_1373l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1378_1, c7_1378_2, c7_1378_3, c7_1378_4, c7_1378_5, c7_1378_6]

end FourColor

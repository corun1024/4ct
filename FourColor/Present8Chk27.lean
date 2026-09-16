import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 27 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1340_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1340_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1340_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1333l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1340_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1333l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1340_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1333l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1340 :
    hubcapFit theRedpart rf8 p8_1333l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1340_1, c8_1340_2, c8_1340_3, c8_1340_4, c8_1340_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1332l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1332l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1342_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1332l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1342 :
    hubcapFit theRedpart rf8 p8_1332l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1342_1, c8_1342_2, c8_1342_3, c8_1342_4, c8_1342_5, c8_1342_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1331l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1331l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1343_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1331l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1343 :
    hubcapFit theRedpart rf8 p8_1331l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1343_1, c8_1343_2, c8_1343_3, c8_1343_4, c8_1343_5, c8_1343_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1345_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1330l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1345_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1330l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1345_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1330l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1345_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1330l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1345_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1330l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1345 :
    hubcapFit theRedpart rf8 p8_1330l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1345_1, c8_1345_2, c8_1345_3, c8_1345_4, c8_1345_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1268l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1268l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1268l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1268l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1268l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1268l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1347_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1268l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1347 :
    hubcapFit theRedpart rf8 p8_1268l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1347_1, c8_1347_2, c8_1347_3, c8_1347_4, c8_1347_5, c8_1347_6, c8_1347_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1267l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1267l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1267l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1267l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1267l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1267l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1349_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1267l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1349 :
    hubcapFit theRedpart rf8 p8_1267l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1349_1, c8_1349_2, c8_1349_3, c8_1349_4, c8_1349_5, c8_1349_6, c8_1349_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1266l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1266l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1351_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1266l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1351 :
    hubcapFit theRedpart rf8 p8_1266l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1351_1, c8_1351_2, c8_1351_3, c8_1351_4, c8_1351_5, c8_1351_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1265l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1352_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1265l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1352 :
    hubcapFit theRedpart rf8 p8_1265l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1352_1, c8_1352_2, c8_1352_3, c8_1352_4, c8_1352_5, c8_1352_6, c8_1352_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1370r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1370r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1370r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1370r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1370r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1370r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1370r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1371_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1370r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1371 :
    hubcapFit theRedpart rf8 p8_1370r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1371_1, c8_1371_2, c8_1371_3, c8_1371_4, c8_1371_5, c8_1371_6, c8_1371_7, c8_1371_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1372_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1370l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1372_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1372_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1370l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1372_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1370l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1372_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1370l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1372 :
    hubcapFit theRedpart rf8 p8_1370l
    (Hubcap.one 2 2 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1372_1, c8_1372_2, c8_1372_3, c8_1372_4, c8_1372_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1374_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1369l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1374_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1369l) (hubSubn 8 6 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1374_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1369l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1374_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1369l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1374 :
    hubcapFit theRedpart rf8 p8_1369l
    (Hubcap.two 0 1 3 <|
     Hubcap.two 2 6 7 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1374_1, c8_1374_2, c8_1374_3, c8_1374_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1375_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1375_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1375_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1368l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1375_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1368l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1375_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1368l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1375 :
    hubcapFit theRedpart rf8 p8_1368l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1375_1, c8_1375_2, c8_1375_3, c8_1375_4, c8_1375_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1377_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1367l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1377_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1367l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1377_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1367l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1377_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1367l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1377_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1367l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1377 :
    hubcapFit theRedpart rf8 p8_1367l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1377_1, c8_1377_2, c8_1377_3, c8_1377_4, c8_1377_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1366l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1366l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1366l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1366l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1366l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1366l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1378_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1366l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1378 :
    hubcapFit theRedpart rf8 p8_1366l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1378_1, c8_1378_2, c8_1378_3, c8_1378_4, c8_1378_5, c8_1378_6, c8_1378_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1384r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1384r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1384r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1384r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1384r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1384r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1384r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1385_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1384r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1385 :
    hubcapFit theRedpart rf8 p8_1384r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1385_1, c8_1385_2, c8_1385_3, c8_1385_4, c8_1385_5, c8_1385_6, c8_1385_7, c8_1385_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1384l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1384l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1384l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1384l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1384l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1386_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1384l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1386 :
    hubcapFit theRedpart rf8 p8_1384l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1386_1, c8_1386_2, c8_1386_3, c8_1386_4, c8_1386_5, c8_1386_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1388_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1383l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1388_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1383l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1388_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1383l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1388_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1383l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1388_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1383l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1388 :
    hubcapFit theRedpart rf8 p8_1383l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1388_1, c8_1388_2, c8_1388_3, c8_1388_4, c8_1388_5]

end FourColor

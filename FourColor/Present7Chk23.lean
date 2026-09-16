import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 23 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1263_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1263_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1257l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1263_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1257l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1263_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1257l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1263_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1257l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1263 :
    hubcapFit theRedpart rf7 p7_1257l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1263_1, c7_1263_2, c7_1263_3, c7_1263_4, c7_1263_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1265_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1256l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1265_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1256l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1265_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1256l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1265_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1256l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1265_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1256l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1265 :
    hubcapFit theRedpart rf7 p7_1256l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1265_1, c7_1265_2, c7_1265_3, c7_1265_4, c7_1265_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1266_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1266_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1255l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1266_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1266_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1255l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1266_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1255l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1266 :
    hubcapFit theRedpart rf7 p7_1255l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1266_1, c7_1266_2, c7_1266_3, c7_1266_4, c7_1266_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1268_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1254l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1268_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1254l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1268_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1254l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1268_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1254l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1268_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1254l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1268 :
    hubcapFit theRedpart rf7 p7_1254l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1268_1, c7_1268_2, c7_1268_3, c7_1268_4, c7_1268_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1279_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1278r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1279_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1278r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1279_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1278r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1279_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1278r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1279_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1278r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1279 :
    hubcapFit theRedpart rf7 p7_1278r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1279_1, c7_1279_2, c7_1279_3, c7_1279_4, c7_1279_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1282_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1281r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1282_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1281r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1282_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1281r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1282_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1281r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1282_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1281r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1282 :
    hubcapFit theRedpart rf7 p7_1281r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1282_1, c7_1282_2, c7_1282_3, c7_1282_4, c7_1282_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1283_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1283_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1283_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1281l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1283_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1281l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1283_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1281l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1283 :
    hubcapFit theRedpart rf7 p7_1281l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1283_1, c7_1283_2, c7_1283_3, c7_1283_4, c7_1283_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1285_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1273l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1285_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1273l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1285_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1273l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1285_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1273l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1285_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1273l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1285 :
    hubcapFit theRedpart rf7 p7_1273l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1285_1, c7_1285_2, c7_1285_3, c7_1285_4, c7_1285_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1287_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1271l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1287_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1271l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1287_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1271l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1287_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1271l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1287_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1271l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1287 :
    hubcapFit theRedpart rf7 p7_1271l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1287_1, c7_1287_2, c7_1287_3, c7_1287_4, c7_1287_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1292r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1292r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1292r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1292r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1292r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1293_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1292r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1293 :
    hubcapFit theRedpart rf7 p7_1292r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1293_1, c7_1293_2, c7_1293_3, c7_1293_4, c7_1293_5, c7_1293_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1307r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1307r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1307r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1307r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1307r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1308_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1307r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1308 :
    hubcapFit theRedpart rf7 p7_1307r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1308_1, c7_1308_2, c7_1308_3, c7_1308_4, c7_1308_5, c7_1308_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1307l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1307l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1307l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1307l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1307l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1307l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1309_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1307l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1309 :
    hubcapFit theRedpart rf7 p7_1307l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1309_1, c7_1309_2, c7_1309_3, c7_1309_4, c7_1309_5, c7_1309_6, c7_1309_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1306l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1306l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1306l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1311_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1311 :
    hubcapFit theRedpart rf7 p7_1306l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1311_1, c7_1311_2, c7_1311_3, c7_1311_4, c7_1311_5, c7_1311_6, c7_1311_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1305l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1305l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1305l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1305l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1305l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1305l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1313_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1305l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1313 :
    hubcapFit theRedpart rf7 p7_1305l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1313_1, c7_1313_2, c7_1313_3, c7_1313_4, c7_1313_5, c7_1313_6, c7_1313_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1303l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1303l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1303l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1303l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1303l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1315_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1303l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1315 :
    hubcapFit theRedpart rf7 p7_1303l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1315_1, c7_1315_2, c7_1315_3, c7_1315_4, c7_1315_5, c7_1315_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1302l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1302l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1302l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1317_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1317 :
    hubcapFit theRedpart rf7 p7_1302l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1317_1, c7_1317_2, c7_1317_3, c7_1317_4, c7_1317_5, c7_1317_6, c7_1317_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1300l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1300l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1300l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1300l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1300l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1300l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1319_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1300l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1319 :
    hubcapFit theRedpart rf7 p7_1300l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1319_1, c7_1319_2, c7_1319_3, c7_1319_4, c7_1319_5, c7_1319_6, c7_1319_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1321_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1321_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1321_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1299l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1321_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1299l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1321_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1299l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1321 :
    hubcapFit theRedpart rf7 p7_1299l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1321_1, c7_1321_2, c7_1321_3, c7_1321_4, c7_1321_5]

end FourColor

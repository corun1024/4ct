import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 26 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1272l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1272l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1272l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1295_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1272l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1295 :
    hubcapFit theRedpart rf8 p8_1272l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1295_1, c8_1295_2, c8_1295_3, c8_1295_4, c8_1295_5, c8_1295_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1308r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1308r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1308r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1308r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1308r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1308r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1308r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1309_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1308r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1309 :
    hubcapFit theRedpart rf8 p8_1308r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1309_1, c8_1309_2, c8_1309_3, c8_1309_4, c8_1309_5, c8_1309_6, c8_1309_7, c8_1309_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1308l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1308l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1308l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1308l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1310_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1308l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1310 :
    hubcapFit theRedpart rf8 p8_1308l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1310_1, c8_1310_2, c8_1310_3, c8_1310_4, c8_1310_5, c8_1310_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1307l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1307l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1312_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1307l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1312 :
    hubcapFit theRedpart rf8 p8_1307l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1312_1, c8_1312_2, c8_1312_3, c8_1312_4, c8_1312_5, c8_1312_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1306l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1306l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1306l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1313_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1306l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1313 :
    hubcapFit theRedpart rf8 p8_1306l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1313_1, c8_1313_2, c8_1313_3, c8_1313_4, c8_1313_5, c8_1313_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1305l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1305l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1305l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1305l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1305l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1315_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1305l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1315 :
    hubcapFit theRedpart rf8 p8_1305l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1315_1, c8_1315_2, c8_1315_3, c8_1315_4, c8_1315_5, c8_1315_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1303l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1303l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1303l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1303l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1303l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1317_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1303l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1317 :
    hubcapFit theRedpart rf8 p8_1303l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1317_1, c8_1317_2, c8_1317_3, c8_1317_4, c8_1317_5, c8_1317_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1318_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1302l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1318_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1302l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1318_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1302l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1318_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1302l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1318_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1302l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1318 :
    hubcapFit theRedpart rf8 p8_1302l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1318_1, c8_1318_2, c8_1318_3, c8_1318_4, c8_1318_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1301l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1301l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1301l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1301l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1301l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1301l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1320_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1301l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1320 :
    hubcapFit theRedpart rf8 p8_1301l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1320_1, c8_1320_2, c8_1320_3, c8_1320_4, c8_1320_5, c8_1320_6, c8_1320_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1300l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1300l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1300l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1322_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1300l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1322 :
    hubcapFit theRedpart rf8 p8_1300l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1322_1, c8_1322_2, c8_1322_3, c8_1322_4, c8_1322_5, c8_1322_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1299l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1299l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1299l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1299l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1299l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1323_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1299l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1323 :
    hubcapFit theRedpart rf8 p8_1299l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1323_1, c8_1323_2, c8_1323_3, c8_1323_4, c8_1323_5, c8_1323_6, c8_1323_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1298l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1298l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1298l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1298l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1298l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1325_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1298l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1325 :
    hubcapFit theRedpart rf8 p8_1298l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1325_1, c8_1325_2, c8_1325_3, c8_1325_4, c8_1325_5, c8_1325_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1297l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1297l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1297l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1326_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1297l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1326 :
    hubcapFit theRedpart rf8 p8_1297l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1326_1, c8_1326_2, c8_1326_3, c8_1326_4, c8_1326_5, c8_1326_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1328_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1270l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1328_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1270l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1328_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1270l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1328_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1270l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1328_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1270l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1328 :
    hubcapFit theRedpart rf8 p8_1270l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1328_1, c8_1328_2, c8_1328_3, c8_1328_4, c8_1328_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1335r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1335r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1335r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1335r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1335r) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1336_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1335r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1336 :
    hubcapFit theRedpart rf8 p8_1335r
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1336_1, c8_1336_2, c8_1336_3, c8_1336_4, c8_1336_5, c8_1336_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1335l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1337_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1335l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1337 :
    hubcapFit theRedpart rf8 p8_1335l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1337_1, c8_1337_2, c8_1337_3, c8_1337_4, c8_1337_5, c8_1337_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1334l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1334l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1334l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1339_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1334l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1339 :
    hubcapFit theRedpart rf8 p8_1334l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1339_1, c8_1339_2, c8_1339_3, c8_1339_4, c8_1339_5, c8_1339_6]

end FourColor

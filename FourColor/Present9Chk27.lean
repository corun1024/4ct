import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 27 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1260l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1260l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1260l) (hubSubn 9 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1282_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1260l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1282 :
    hubcapFit theRedpart rf9 p9_1260l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1282_1, c9_1282_2, c9_1282_3, c9_1282_4, c9_1282_5, c9_1282_6, c9_1282_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1259l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1259l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1259l) (hubSubn 9 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1284_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1259l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1284 :
    hubcapFit theRedpart rf9 p9_1259l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1284_1, c9_1284_2, c9_1284_3, c9_1284_4, c9_1284_5, c9_1284_6, c9_1284_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1258l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1258l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1258l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1286_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1258l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1286 :
    hubcapFit theRedpart rf9 p9_1258l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1286_1, c9_1286_2, c9_1286_3, c9_1286_4, c9_1286_5, c9_1286_6, c9_1286_7, c9_1286_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1134l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1134l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1134l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1134l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1134l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1288_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1134l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1288 :
    hubcapFit theRedpart rf9 p9_1134l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1288_1, c9_1288_2, c9_1288_3, c9_1288_4, c9_1288_5, c9_1288_6, c9_1288_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1133l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1133l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1133l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1290_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1133l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1290 :
    hubcapFit theRedpart rf9 p9_1133l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1290_1, c9_1290_2, c9_1290_3, c9_1290_4, c9_1290_5, c9_1290_6, c9_1290_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1132l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1132l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1132l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1132l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1292_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1132l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1292 :
    hubcapFit theRedpart rf9 p9_1132l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1292_1, c9_1292_2, c9_1292_3, c9_1292_4, c9_1292_5, c9_1292_6, c9_1292_7, c9_1292_8, c9_1292_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1131l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1131l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1131l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1131l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1131l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1131l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1131l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1131l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1294_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1131l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1294 :
    hubcapFit theRedpart rf9 p9_1131l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1294_1, c9_1294_2, c9_1294_3, c9_1294_4, c9_1294_5, c9_1294_6, c9_1294_7, c9_1294_8, c9_1294_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1296l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1296l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1296l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1296l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1296l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1296l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1296l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1297_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1296l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1297 :
    hubcapFit theRedpart rf9 p9_1296l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1297_1, c9_1297_2, c9_1297_3, c9_1297_4, c9_1297_5, c9_1297_6, c9_1297_7, c9_1297_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1300l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1300l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1300l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1300l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1301_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1300l) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1301 :
    hubcapFit theRedpart rf9 p9_1300l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1301_1, c9_1301_2, c9_1301_3, c9_1301_4, c9_1301_5, c9_1301_6, c9_1301_7, c9_1301_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1300r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1300r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1300r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1300r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1300r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1300r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1303_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1300r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1303 :
    hubcapFit theRedpart rf9 p9_1300r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1303_1, c9_1303_2, c9_1303_3, c9_1303_4, c9_1303_5, c9_1303_6, c9_1303_7, c9_1303_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1299r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1299r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1299r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1299r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1299r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1299r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1299r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1306_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1299r) (hubSubn 9 2 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1306 :
    hubcapFit theRedpart rf9 p9_1299r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1306_1, c9_1306_2, c9_1306_3, c9_1306_4, c9_1306_5, c9_1306_6, c9_1306_7, c9_1306_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_919l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1310_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1310 :
    hubcapFit theRedpart rf9 p9_919l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1310_1, c9_1310_2, c9_1310_3, c9_1310_4, c9_1310_5, c9_1310_6, c9_1310_7, c9_1310_8, c9_1310_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_918l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_918l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_918l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1312_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_918l) (hubSubn 9 5 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1312 :
    hubcapFit theRedpart rf9 p9_918l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1312_1, c9_1312_2, c9_1312_3, c9_1312_4, c9_1312_5, c9_1312_6, c9_1312_7, c9_1312_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1335r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1335r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1335r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1335r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1335r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1335r) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1336_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1335r) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1336 :
    hubcapFit theRedpart rf9 p9_1335r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1336_1, c9_1336_2, c9_1336_3, c9_1336_4, c9_1336_5, c9_1336_6, c9_1336_7]

end FourColor

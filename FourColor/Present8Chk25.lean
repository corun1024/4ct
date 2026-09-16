import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 25 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1231l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1231l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1231l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1231l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1231l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1247_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1231l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1247 :
    hubcapFit theRedpart rf8 p8_1231l
    (Hubcap.one 1 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1247_1, c8_1247_2, c8_1247_3, c8_1247_4, c8_1247_5, c8_1247_6, c8_1247_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1230l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1230l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1230l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1230l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1230l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1249_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1230l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1249 :
    hubcapFit theRedpart rf8 p8_1230l
    (Hubcap.one 1 1 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1249_1, c8_1249_2, c8_1249_3, c8_1249_4, c8_1249_5, c8_1249_6, c8_1249_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1229l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1229l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1229l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1229l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1229l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1251_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1229l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1251 :
    hubcapFit theRedpart rf8 p8_1229l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1251_1, c8_1251_2, c8_1251_3, c8_1251_4, c8_1251_5, c8_1251_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1228l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1228l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1228l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1228l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1252_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1228l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1252 :
    hubcapFit theRedpart rf8 p8_1228l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1252_1, c8_1252_2, c8_1252_3, c8_1252_4, c8_1252_5, c8_1252_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1227l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1227l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1227l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1227l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1254_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1227l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1254 :
    hubcapFit theRedpart rf8 p8_1227l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1254_1, c8_1254_2, c8_1254_3, c8_1254_4, c8_1254_5, c8_1254_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1256_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1225l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1256_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1225l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1256_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1225l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1256_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1225l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1256_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1225l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1256 :
    hubcapFit theRedpart rf8 p8_1225l
    (Hubcap.one 2 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1256_1, c8_1256_2, c8_1256_3, c8_1256_4, c8_1256_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1259_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1184l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1259_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1184l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1259_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1184l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1259_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1184l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1259_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1184l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1259 :
    hubcapFit theRedpart rf8 p8_1184l
    (Hubcap.one 1 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1259_1, c8_1259_2, c8_1259_3, c8_1259_4, c8_1259_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1183l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1183l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1183l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1183l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1260_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1183l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1260 :
    hubcapFit theRedpart rf8 p8_1183l
    (Hubcap.one 0 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1260_1, c8_1260_2, c8_1260_3, c8_1260_4, c8_1260_5, c8_1260_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1182l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1182l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1182l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1182l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1262_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1182l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1262 :
    hubcapFit theRedpart rf8 p8_1182l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1262_1, c8_1262_2, c8_1262_3, c8_1262_4, c8_1262_5, c8_1262_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1263_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1181l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1263_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1181l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1263_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1181l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1263_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1181l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1263_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1181l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1263 :
    hubcapFit theRedpart rf8 p8_1181l
    (Hubcap.one 3 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1263_1, c8_1263_2, c8_1263_3, c8_1263_4, c8_1263_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1282r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1282r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1282r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1282r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1282r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1282r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1283_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1282r) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1283 :
    hubcapFit theRedpart rf8 p8_1282r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1283_1, c8_1283_2, c8_1283_3, c8_1283_4, c8_1283_5, c8_1283_6, c8_1283_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1284_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1282l) (hubSubn 8 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1284 :
    hubcapFit theRedpart rf8 p8_1282l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1284_1, c8_1284_2, c8_1284_3, c8_1284_4, c8_1284_5, c8_1284_6, c8_1284_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1280l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1280l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1286_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1280l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1286 :
    hubcapFit theRedpart rf8 p8_1280l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1286_1, c8_1286_2, c8_1286_3, c8_1286_4, c8_1286_5, c8_1286_6, c8_1286_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1279l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1279l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1279l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1288_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1279l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1288 :
    hubcapFit theRedpart rf8 p8_1279l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1288_1, c8_1288_2, c8_1288_3, c8_1288_4, c8_1288_5, c8_1288_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1276l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1276l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1276l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1276l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1276l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1290_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1276l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1290 :
    hubcapFit theRedpart rf8 p8_1276l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1290_1, c8_1290_2, c8_1290_3, c8_1290_4, c8_1290_5, c8_1290_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1274l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1274l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1274l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1274l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1292_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1274l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1292 :
    hubcapFit theRedpart rf8 p8_1274l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1292_1, c8_1292_2, c8_1292_3, c8_1292_4, c8_1292_5, c8_1292_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1294_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1273l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1294_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1273l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1294_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1273l) (hubSubn 8 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1294_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1273l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1294_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1273l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1294 :
    hubcapFit theRedpart rf8 p8_1273l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1294_1, c8_1294_2, c8_1294_3, c8_1294_4, c8_1294_5]

end FourColor

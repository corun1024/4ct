import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 24 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1192l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1192l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1192l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1192l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1192l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1194_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1192l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1194 :
    hubcapFit theRedpart rf8 p8_1192l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1194_1, c8_1194_2, c8_1194_3, c8_1194_4, c8_1194_5, c8_1194_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1191l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1191l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1191l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1191l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1191l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1196_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1191l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1196 :
    hubcapFit theRedpart rf8 p8_1191l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1196_1, c8_1196_2, c8_1196_3, c8_1196_4, c8_1196_5, c8_1196_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1190l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1190l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1190l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1190l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1190l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1197_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1190l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1197 :
    hubcapFit theRedpart rf8 p8_1190l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1197_1, c8_1197_2, c8_1197_3, c8_1197_4, c8_1197_5, c8_1197_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1189l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1189l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1199_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1189l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1199 :
    hubcapFit theRedpart rf8 p8_1189l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1199_1, c8_1199_2, c8_1199_3, c8_1199_4, c8_1199_5, c8_1199_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1210r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1210r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1210r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1210r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1210r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1210r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1211_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1210r) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1211 :
    hubcapFit theRedpart rf8 p8_1210r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1211_1, c8_1211_2, c8_1211_3, c8_1211_4, c8_1211_5, c8_1211_6, c8_1211_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1210l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1210l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1210l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1210l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1210l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1212_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1212 :
    hubcapFit theRedpart rf8 p8_1210l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1212_1, c8_1212_2, c8_1212_3, c8_1212_4, c8_1212_5, c8_1212_6, c8_1212_7, c8_1212_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1209l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1209l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1209l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1209l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1209l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1209l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1209l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1214_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1209l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1214 :
    hubcapFit theRedpart rf8 p8_1209l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1214_1, c8_1214_2, c8_1214_3, c8_1214_4, c8_1214_5, c8_1214_6, c8_1214_7, c8_1214_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1206l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1216_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1206l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1216 :
    hubcapFit theRedpart rf8 p8_1206l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1216_1, c8_1216_2, c8_1216_3, c8_1216_4, c8_1216_5, c8_1216_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1218_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1205l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1218_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1205l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1218_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1205l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1218_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1205l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1218_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1205l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1218 :
    hubcapFit theRedpart rf8 p8_1205l
    (Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1218_1, c8_1218_2, c8_1218_3, c8_1218_4, c8_1218_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1204l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1204l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1204l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1219_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1204l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1219 :
    hubcapFit theRedpart rf8 p8_1204l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1219_1, c8_1219_2, c8_1219_3, c8_1219_4, c8_1219_5, c8_1219_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1203l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1203l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1221_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1203l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1221 :
    hubcapFit theRedpart rf8 p8_1203l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1221_1, c8_1221_2, c8_1221_3, c8_1221_4, c8_1221_5, c8_1221_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1222_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1202l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1222_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1222_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1202l) (hubSubn 8 4 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1222_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1202l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1222_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1202l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1222 :
    hubcapFit theRedpart rf8 p8_1202l
    (Hubcap.one 1 1 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 4 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1222_1, c8_1222_2, c8_1222_3, c8_1222_4, c8_1222_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1238r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1238r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1238r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1238r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1238r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1239_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1238r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1239 :
    hubcapFit theRedpart rf8 p8_1238r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1239_1, c8_1239_2, c8_1239_3, c8_1239_4, c8_1239_5, c8_1239_6, c8_1239_7, c8_1239_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1238l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1238l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1238l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1238l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1240_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1238l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1240 :
    hubcapFit theRedpart rf8 p8_1238l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1240_1, c8_1240_2, c8_1240_3, c8_1240_4, c8_1240_5, c8_1240_6, c8_1240_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1237l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1237l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1237l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1242_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1237l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1242 :
    hubcapFit theRedpart rf8 p8_1237l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1242_1, c8_1242_2, c8_1242_3, c8_1242_4, c8_1242_5, c8_1242_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1235l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1235l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1235l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1235l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1235l) (hubSubn 8 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1244_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1235l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1244 :
    hubcapFit theRedpart rf8 p8_1235l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1244_1, c8_1244_2, c8_1244_3, c8_1244_4, c8_1244_5, c8_1244_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1245_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1234l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1245_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1234l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1245_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1234l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1245_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1234l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1245_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1234l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1245 :
    hubcapFit theRedpart rf8 p8_1234l
    (Hubcap.one 2 1 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1245_1, c8_1245_2, c8_1245_3, c8_1245_4, c8_1245_5]

end FourColor

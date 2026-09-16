import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 22 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1205r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1205r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1205r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1205r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1205r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1205r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1206_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1205r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1206 :
    hubcapFit theRedpart rf7 p7_1205r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1206_1, c7_1206_2, c7_1206_3, c7_1206_4, c7_1206_5, c7_1206_6, c7_1206_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1208_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1202l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1208_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1202l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1208_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1202l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1208_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1202l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1208 :
    hubcapFit theRedpart rf7 p7_1202l
    (Hubcap.one 5 2 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1208_1, c7_1208_2, c7_1208_3, c7_1208_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1210_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1201l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1210_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1201l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1210_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1201l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1210_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1201l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1210_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1201l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1210 :
    hubcapFit theRedpart rf7 p7_1201l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1210_1, c7_1210_2, c7_1210_3, c7_1210_4, c7_1210_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1211r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1211r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1211r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1211r) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1211r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1212_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1211r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1212 :
    hubcapFit theRedpart rf7 p7_1211r
    (Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1212_1, c7_1212_2, c7_1212_3, c7_1212_4, c7_1212_5, c7_1212_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1220r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1220r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1220r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1220r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1220r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1221_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1220r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1221 :
    hubcapFit theRedpart rf7 p7_1220r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1221_1, c7_1221_2, c7_1221_3, c7_1221_4, c7_1221_5, c7_1221_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1227r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1227r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1227r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1227r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1227r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1227r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1228_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1227r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1228 :
    hubcapFit theRedpart rf7 p7_1227r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1228_1, c7_1228_2, c7_1228_3, c7_1228_4, c7_1228_5, c7_1228_6, c7_1228_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1227l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1227l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1227l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1227l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1229_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1227l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1229 :
    hubcapFit theRedpart rf7 p7_1227l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1229_1, c7_1229_2, c7_1229_3, c7_1229_4, c7_1229_5, c7_1229_6, c7_1229_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1226l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1226l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1226l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1226l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1231_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1226l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1231 :
    hubcapFit theRedpart rf7 p7_1226l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1231_1, c7_1231_2, c7_1231_3, c7_1231_4, c7_1231_5, c7_1231_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1224l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1224l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1224l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1224l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1224l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1233_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1224l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1233 :
    hubcapFit theRedpart rf7 p7_1224l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1233_1, c7_1233_2, c7_1233_3, c7_1233_4, c7_1233_5, c7_1233_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1223l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1223l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1223l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1223l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1223l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1234_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1223l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1234 :
    hubcapFit theRedpart rf7 p7_1223l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1234_1, c7_1234_2, c7_1234_3, c7_1234_4, c7_1234_5, c7_1234_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1236_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1215l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1236_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1215l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1236_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1215l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1236_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1215l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1236_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1215l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1236 :
    hubcapFit theRedpart rf7 p7_1215l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1236_1, c7_1236_2, c7_1236_3, c7_1236_4, c7_1236_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1243r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1243r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1243r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1243r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1243r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1244_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1243r) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1244 :
    hubcapFit theRedpart rf7 p7_1243r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 2 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1244_1, c7_1244_2, c7_1244_3, c7_1244_4, c7_1244_5, c7_1244_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1243l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1243l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1243l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1243l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1243l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1245_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1245 :
    hubcapFit theRedpart rf7 p7_1243l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1245_1, c7_1245_2, c7_1245_3, c7_1245_4, c7_1245_5, c7_1245_6, c7_1245_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1247_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1242l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1247_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1242l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1247_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1242l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1247_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1242l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1247_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1242l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1247 :
    hubcapFit theRedpart rf7 p7_1242l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1247_1, c7_1247_2, c7_1247_3, c7_1247_4, c7_1247_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1249_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1248r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1249_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1248r) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1249_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1248r) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1249_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1248r) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1249 :
    hubcapFit theRedpart rf7 p7_1248r
    (Hubcap.one 2 1 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 3 5 1 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1249_1, c7_1249_2, c7_1249_3, c7_1249_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1240l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1240l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1240l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1240l) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1240l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1251_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1240l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1251 :
    hubcapFit theRedpart rf7 p7_1240l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1251_1, c7_1251_2, c7_1251_3, c7_1251_4, c7_1251_5, c7_1251_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1252_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1239l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1252_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1239l) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1252_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1239l) (hubSubn 7 4 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1252_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1239l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1252 :
    hubcapFit theRedpart rf7 p7_1239l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 1 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1252_1, c7_1252_2, c7_1252_3, c7_1252_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1260r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1260r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1260r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1260r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1260r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1261_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1260r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1261 :
    hubcapFit theRedpart rf7 p7_1260r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1261_1, c7_1261_2, c7_1261_3, c7_1261_4, c7_1261_5, c7_1261_6]

end FourColor

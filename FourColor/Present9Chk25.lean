import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 25 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1176r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1176r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1176r) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1176r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1177_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1176r) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1177 :
    hubcapFit theRedpart rf9 p9_1176r
    (Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1177_1, c9_1177_2, c9_1177_3, c9_1177_4, c9_1177_5, c9_1177_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1176l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1178_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1176l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1178 :
    hubcapFit theRedpart rf9 p9_1176l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1178_1, c9_1178_2, c9_1178_3, c9_1178_4, c9_1178_5, c9_1178_6, c9_1178_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1174l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1180_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1174l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1180 :
    hubcapFit theRedpart rf9 p9_1174l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1180_1, c9_1180_2, c9_1180_3, c9_1180_4, c9_1180_5, c9_1180_6, c9_1180_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1173l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1173l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1173l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1182_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1173l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1182 :
    hubcapFit theRedpart rf9 p9_1173l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1182_1, c9_1182_2, c9_1182_3, c9_1182_4, c9_1182_5, c9_1182_6, c9_1182_7, c9_1182_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1172l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1172l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1184_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1172l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1184 :
    hubcapFit theRedpart rf9 p9_1172l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1184_1, c9_1184_2, c9_1184_3, c9_1184_4, c9_1184_5, c9_1184_6, c9_1184_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1171l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1171l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1171l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1186_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1171l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1186 :
    hubcapFit theRedpart rf9 p9_1171l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1186_1, c9_1186_2, c9_1186_3, c9_1186_4, c9_1186_5, c9_1186_6, c9_1186_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1189l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1189l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1189l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1189l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1189l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1190_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1189l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1190 :
    hubcapFit theRedpart rf9 p9_1189l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1190_1, c9_1190_2, c9_1190_3, c9_1190_4, c9_1190_5, c9_1190_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1192l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1192l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1192l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1192l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1192l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1193_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1192l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1193 :
    hubcapFit theRedpart rf9 p9_1192l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1193_1, c9_1193_2, c9_1193_3, c9_1193_4, c9_1193_5, c9_1193_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1192r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1192r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1192r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1192r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1192r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1195_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1192r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1195 :
    hubcapFit theRedpart rf9 p9_1192r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1195_1, c9_1195_2, c9_1195_3, c9_1195_4, c9_1195_5, c9_1195_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1200l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1200l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1201_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1200l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1201 :
    hubcapFit theRedpart rf9 p9_1200l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1201_1, c9_1201_2, c9_1201_3, c9_1201_4, c9_1201_5, c9_1201_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1200r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1200r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1200r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1200r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1200r) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1203_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1200r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1203 :
    hubcapFit theRedpart rf9 p9_1200r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1203_1, c9_1203_2, c9_1203_3, c9_1203_4, c9_1203_5, c9_1203_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1206l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1206l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1207_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1206l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1207 :
    hubcapFit theRedpart rf9 p9_1206l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1207_1, c9_1207_2, c9_1207_3, c9_1207_4, c9_1207_5, c9_1207_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1206r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1206r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1206r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1206r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1206r) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1209_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1206r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1209 :
    hubcapFit theRedpart rf9 p9_1206r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1209_1, c9_1209_2, c9_1209_3, c9_1209_4, c9_1209_5, c9_1209_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1214l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1214l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1214l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1215_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1214l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1215 :
    hubcapFit theRedpart rf9 p9_1214l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1215_1, c9_1215_2, c9_1215_3, c9_1215_4, c9_1215_5, c9_1215_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1214r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1214r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1214r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1214r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1217_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1214r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1217 :
    hubcapFit theRedpart rf9 p9_1214r
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1217_1, c9_1217_2, c9_1217_3, c9_1217_4, c9_1217_5, c9_1217_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1220l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1220l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1220l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1220l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1220l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1221_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1220l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1221 :
    hubcapFit theRedpart rf9 p9_1220l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1221_1, c9_1221_2, c9_1221_3, c9_1221_4, c9_1221_5, c9_1221_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1220r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1220r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1220r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1220r) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1220r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1223_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1220r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1223 :
    hubcapFit theRedpart rf9 p9_1220r
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1223_1, c9_1223_2, c9_1223_3, c9_1223_4, c9_1223_5, c9_1223_6]

end FourColor

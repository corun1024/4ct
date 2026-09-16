import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 21 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1154r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1154r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1154r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1154r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1154r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1154r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1155_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1154r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1155 :
    hubcapFit theRedpart rf7 p7_1154r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1155_1, c7_1155_2, c7_1155_3, c7_1155_4, c7_1155_5, c7_1155_6, c7_1155_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1154l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1154l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1154l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1154l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1154l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1156_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1154l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1156 :
    hubcapFit theRedpart rf7 p7_1154l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1156_1, c7_1156_2, c7_1156_3, c7_1156_4, c7_1156_5, c7_1156_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1153l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1158_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1153l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1158 :
    hubcapFit theRedpart rf7 p7_1153l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1158_1, c7_1158_2, c7_1158_3, c7_1158_4, c7_1158_5, c7_1158_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1151l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1151l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1151l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1151l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1151l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1151l) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1160_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1151l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1160 :
    hubcapFit theRedpart rf7 p7_1151l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1160_1, c7_1160_2, c7_1160_3, c7_1160_4, c7_1160_5, c7_1160_6, c7_1160_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1167_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1166r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1167_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1166r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1167_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1166r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1167_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1166r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1167_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1166r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1167 :
    hubcapFit theRedpart rf7 p7_1166r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1167_1, c7_1167_2, c7_1167_3, c7_1167_4, c7_1167_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1166l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1166l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1166l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1166l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1168_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1166l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1168 :
    hubcapFit theRedpart rf7 p7_1166l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1168_1, c7_1168_2, c7_1168_3, c7_1168_4, c7_1168_5, c7_1168_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1171r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1171r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1171r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1171r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1171r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1171r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1172_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1171r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1172 :
    hubcapFit theRedpart rf7 p7_1171r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1172_1, c7_1172_2, c7_1172_3, c7_1172_4, c7_1172_5, c7_1172_6, c7_1172_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1173_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1171l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1173_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1171l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1173_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1171l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1173_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1171l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1173 :
    hubcapFit theRedpart rf7 p7_1171l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1173_1, c7_1173_2, c7_1173_3, c7_1173_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1175_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1170l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1175_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1170l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1175_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1170l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1175_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1170l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1175 :
    hubcapFit theRedpart rf7 p7_1170l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1175_1, c7_1175_2, c7_1175_3, c7_1175_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1163l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1163l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1163l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1163l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1163l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1177_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1163l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1177 :
    hubcapFit theRedpart rf7 p7_1163l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1177_1, c7_1177_2, c7_1177_3, c7_1177_4, c7_1177_5, c7_1177_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1181r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1181r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1181r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1181r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1181r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1182_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1181r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1182 :
    hubcapFit theRedpart rf7 p7_1181r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1182_1, c7_1182_2, c7_1182_3, c7_1182_4, c7_1182_5, c7_1182_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1181l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1181l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1181l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1183_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1181l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1183 :
    hubcapFit theRedpart rf7 p7_1181l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1183_1, c7_1183_2, c7_1183_3, c7_1183_4, c7_1183_5, c7_1183_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1185_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1185_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1180l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1185_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1180l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1185_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1180l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1185_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1180l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1185 :
    hubcapFit theRedpart rf7 p7_1180l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1185_1, c7_1185_2, c7_1185_3, c7_1185_4, c7_1185_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1187r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1187r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1187r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1187r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1187r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1187r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1188_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1187r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1188 :
    hubcapFit theRedpart rf7 p7_1187r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1188_1, c7_1188_2, c7_1188_3, c7_1188_4, c7_1188_5, c7_1188_6, c7_1188_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1187l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1187l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1187l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1187l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1187l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1189_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1187l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1189 :
    hubcapFit theRedpart rf7 p7_1187l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1189_1, c7_1189_2, c7_1189_3, c7_1189_4, c7_1189_5, c7_1189_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1186l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1186l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1186l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1186l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1186l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1191_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1186l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1191 :
    hubcapFit theRedpart rf7 p7_1186l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1191_1, c7_1191_2, c7_1191_3, c7_1191_4, c7_1191_5, c7_1191_6, c7_1191_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1178l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1178l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1194_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1178l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1194 :
    hubcapFit theRedpart rf7 p7_1178l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1194_1, c7_1194_2, c7_1194_3, c7_1194_4, c7_1194_5, c7_1194_6]

end FourColor

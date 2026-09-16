import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 23 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1142l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1142l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1142l) (hubSubn 8 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1142l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1142l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1144_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1142l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1144 :
    hubcapFit theRedpart rf8 p8_1142l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1144_1, c8_1144_2, c8_1144_3, c8_1144_4, c8_1144_5, c8_1144_6, c8_1144_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1146r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1146r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1146r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1146r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1147_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1146r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1147 :
    hubcapFit theRedpart rf8 p8_1146r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1147_1, c8_1147_2, c8_1147_3, c8_1147_4, c8_1147_5, c8_1147_6, c8_1147_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1148_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1148_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1148_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1146l) (hubSubn 8 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1148_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1146l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1148_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1146l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1148 :
    hubcapFit theRedpart rf8 p8_1146l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1148_1, c8_1148_2, c8_1148_3, c8_1148_4, c8_1148_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1140l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1140l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1150_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1140l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1150 :
    hubcapFit theRedpart rf8 p8_1140l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1150_1, c8_1150_2, c8_1150_3, c8_1150_4, c8_1150_5, c8_1150_6, c8_1150_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1154r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1154r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1154r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1154r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1154r) (hubSubn 8 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1155_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1154r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1155 :
    hubcapFit theRedpart rf8 p8_1154r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1155_1, c8_1155_2, c8_1155_3, c8_1155_4, c8_1155_5, c8_1155_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1156_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1154l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1156_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1154l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1156_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1154l) (hubSubn 8 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1156_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1154l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1156_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1154l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1156 :
    hubcapFit theRedpart rf8 p8_1154l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1156_1, c8_1156_2, c8_1156_3, c8_1156_4, c8_1156_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1153l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1153l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1153l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1153l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1158_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1153l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1158 :
    hubcapFit theRedpart rf8 p8_1153l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1158_1, c8_1158_2, c8_1158_3, c8_1158_4, c8_1158_5, c8_1158_6, c8_1158_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1152l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1152l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1152l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1152l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1152l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1160_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1152l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1160 :
    hubcapFit theRedpart rf8 p8_1152l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1160_1, c8_1160_2, c8_1160_3, c8_1160_4, c8_1160_5, c8_1160_6, c8_1160_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1138l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1138l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1138l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1138l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1138l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1162_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1138l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1162 :
    hubcapFit theRedpart rf8 p8_1138l
    (Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1162_1, c8_1162_2, c8_1162_3, c8_1162_4, c8_1162_5, c8_1162_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1137l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1137l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1137l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1164_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1137l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1164 :
    hubcapFit theRedpart rf8 p8_1137l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1164_1, c8_1164_2, c8_1164_3, c8_1164_4, c8_1164_5, c8_1164_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1136l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1136l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1136l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1136l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1136l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1165_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1136l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1165 :
    hubcapFit theRedpart rf8 p8_1136l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1165_1, c8_1165_2, c8_1165_3, c8_1165_4, c8_1165_5, c8_1165_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1044l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1044l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1044l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1044l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1044l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1044l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1167_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1044l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1167 :
    hubcapFit theRedpart rf8 p8_1044l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1167_1, c8_1167_2, c8_1167_3, c8_1167_4, c8_1167_5, c8_1167_6, c8_1167_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1043l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1043l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1043l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1043l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1043l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1043l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1169_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1043l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1169 :
    hubcapFit theRedpart rf8 p8_1043l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1169_1, c8_1169_2, c8_1169_3, c8_1169_4, c8_1169_5, c8_1169_6, c8_1169_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_736l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_736l) (hubSubn 8 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1171_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_736l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1171 :
    hubcapFit theRedpart rf8 p8_736l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1171_1, c8_1171_2, c8_1171_3, c8_1171_4, c8_1171_5, c8_1171_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_735l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_735l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1173_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_735l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1173 :
    hubcapFit theRedpart rf8 p8_735l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1173_1, c8_1173_2, c8_1173_3, c8_1173_4, c8_1173_5, c8_1173_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_734l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_734l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_734l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1174_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_734l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1174 :
    hubcapFit theRedpart rf8 p8_734l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1174_1, c8_1174_2, c8_1174_3, c8_1174_4, c8_1174_5, c8_1174_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1192r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1192r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1192r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1192r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1192r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1192r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1193_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1192r) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1193 :
    hubcapFit theRedpart rf8 p8_1192r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1193_1, c8_1193_2, c8_1193_3, c8_1193_4, c8_1193_5, c8_1193_6, c8_1193_7]

end FourColor

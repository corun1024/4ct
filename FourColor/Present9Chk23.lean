import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 23 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1021l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1021l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1021l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1021l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1021l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1021l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1072_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1021l) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1072 :
    hubcapFit theRedpart rf9 p9_1021l
    (Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1072_1, c9_1072_2, c9_1072_3, c9_1072_4, c9_1072_5, c9_1072_6, c9_1072_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1076r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1076r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1076r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1076r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1076r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1076r) (hubSubn 9 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1077_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1076r) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1077 :
    hubcapFit theRedpart rf9 p9_1076r
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1077_1, c9_1077_2, c9_1077_3, c9_1077_4, c9_1077_5, c9_1077_6, c9_1077_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1076l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1076l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1076l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1076l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1076l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1076l) (hubSubn 9 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1078_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1076l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1078 :
    hubcapFit theRedpart rf9 p9_1076l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1078_1, c9_1078_2, c9_1078_3, c9_1078_4, c9_1078_5, c9_1078_6, c9_1078_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1080l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1080l) (hubSubn 9 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1081_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1080l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1081 :
    hubcapFit theRedpart rf9 p9_1080l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1081_1, c9_1081_2, c9_1081_3, c9_1081_4, c9_1081_5, c9_1081_6, c9_1081_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1080r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1080r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1080r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1080r) (hubSubn 9 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1083_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1080r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1083 :
    hubcapFit theRedpart rf9 p9_1080r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1083_1, c9_1083_2, c9_1083_3, c9_1083_4, c9_1083_5, c9_1083_6, c9_1083_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1086l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1086l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1086l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1086l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1087_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1086l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1087 :
    hubcapFit theRedpart rf9 p9_1086l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1087_1, c9_1087_2, c9_1087_3, c9_1087_4, c9_1087_5, c9_1087_6, c9_1087_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1086r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1086r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1086r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1086r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1086r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1086r) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1089_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1086r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1089 :
    hubcapFit theRedpart rf9 p9_1086r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1089_1, c9_1089_2, c9_1089_3, c9_1089_4, c9_1089_5, c9_1089_6, c9_1089_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1097r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1097r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1097r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1097r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1097r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1097r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1097r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1098_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1097r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1098 :
    hubcapFit theRedpart rf9 p9_1097r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1098_1, c9_1098_2, c9_1098_3, c9_1098_4, c9_1098_5, c9_1098_6, c9_1098_7, c9_1098_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1097l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1097l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1097l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1097l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1097l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1097l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1097l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1099_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1097l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1099 :
    hubcapFit theRedpart rf9 p9_1097l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1099_1, c9_1099_2, c9_1099_3, c9_1099_4, c9_1099_5, c9_1099_6, c9_1099_7, c9_1099_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1096l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1096l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1096l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1096l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1096l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1096l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1096l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1096l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1101_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1096l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1101 :
    hubcapFit theRedpart rf9 p9_1096l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1101_1, c9_1101_2, c9_1101_3, c9_1101_4, c9_1101_5, c9_1101_6, c9_1101_7, c9_1101_8, c9_1101_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1095l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1095l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1103_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1103 :
    hubcapFit theRedpart rf9 p9_1095l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1103_1, c9_1103_2, c9_1103_3, c9_1103_4, c9_1103_5, c9_1103_6, c9_1103_7, c9_1103_8, c9_1103_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1093l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1093l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1093l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1093l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1093l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1105_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1093l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1105 :
    hubcapFit theRedpart rf9 p9_1093l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1105_1, c9_1105_2, c9_1105_3, c9_1105_4, c9_1105_5, c9_1105_6, c9_1105_7, c9_1105_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1092l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1092l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1092l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1092l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1092l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1107_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1092l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1107 :
    hubcapFit theRedpart rf9 p9_1092l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1107_1, c9_1107_2, c9_1107_3, c9_1107_4, c9_1107_5, c9_1107_6, c9_1107_7, c9_1107_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1112r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1112r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1112r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1112r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1112r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1113_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1112r) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1113 :
    hubcapFit theRedpart rf9 p9_1112r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1113_1, c9_1113_2, c9_1113_3, c9_1113_4, c9_1113_5, c9_1113_6, c9_1113_7, c9_1113_8]

end FourColor

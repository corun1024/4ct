import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 20 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1092_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1052l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1092_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1052l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1092_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1052l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1092_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1052l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1092_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1052l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1092 :
    hubcapFit theRedpart rf7 p7_1052l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1092_1, c7_1092_2, c7_1092_3, c7_1092_4, c7_1092_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1051l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1051l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1051l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1051l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1094_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1051l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1094 :
    hubcapFit theRedpart rf7 p7_1051l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1094_1, c7_1094_2, c7_1094_3, c7_1094_4, c7_1094_5, c7_1094_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1117r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1117r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1117r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1117r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1117r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1117r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1118_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1117r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1118 :
    hubcapFit theRedpart rf7 p7_1117r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1118_1, c7_1118_2, c7_1118_3, c7_1118_4, c7_1118_5, c7_1118_6, c7_1118_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1117l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1117l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1117l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1117l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1119_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1119 :
    hubcapFit theRedpart rf7 p7_1117l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1119_1, c7_1119_2, c7_1119_3, c7_1119_4, c7_1119_5, c7_1119_6, c7_1119_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1115l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1115l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1121_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1115l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1121 :
    hubcapFit theRedpart rf7 p7_1115l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1121_1, c7_1121_2, c7_1121_3, c7_1121_4, c7_1121_5, c7_1121_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1129r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1129r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1129r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1129r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1129r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1130_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1129r) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1130 :
    hubcapFit theRedpart rf7 p7_1129r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1130_1, c7_1130_2, c7_1130_3, c7_1130_4, c7_1130_5, c7_1130_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1129l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1129l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1129l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1131_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1129l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1131 :
    hubcapFit theRedpart rf7 p7_1129l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1131_1, c7_1131_2, c7_1131_3, c7_1131_4, c7_1131_5, c7_1131_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1127l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1127l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1127l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1127l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1133_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1127l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1133 :
    hubcapFit theRedpart rf7 p7_1127l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1133_1, c7_1133_2, c7_1133_3, c7_1133_4, c7_1133_5, c7_1133_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1126l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1126l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1126l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1126l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1126l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1126l) (hubSubn 7 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1135_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1126l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1135 :
    hubcapFit theRedpart rf7 p7_1126l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1135_1, c7_1135_2, c7_1135_3, c7_1135_4, c7_1135_5, c7_1135_6, c7_1135_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1125l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1125l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1125l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1137_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1125l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1137 :
    hubcapFit theRedpart rf7 p7_1125l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1137_1, c7_1137_2, c7_1137_3, c7_1137_4, c7_1137_5, c7_1137_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1124l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1124l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1124l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1124l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1124l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1138_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1124l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1138 :
    hubcapFit theRedpart rf7 p7_1124l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1138_1, c7_1138_2, c7_1138_3, c7_1138_4, c7_1138_5, c7_1138_6, c7_1138_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1123l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1123l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1123l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1123l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1123l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1140_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1123l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1140 :
    hubcapFit theRedpart rf7 p7_1123l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1140_1, c7_1140_2, c7_1140_3, c7_1140_4, c7_1140_5, c7_1140_6, c7_1140_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1142_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1113l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1142_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1113l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1142_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1142_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1113l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1142_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1113l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1142 :
    hubcapFit theRedpart rf7 p7_1113l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1142_1, c7_1142_2, c7_1142_3, c7_1142_4, c7_1142_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1144_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1112l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1144_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1112l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1144_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1144_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1112l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1144_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1112l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1144 :
    hubcapFit theRedpart rf7 p7_1112l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1144_1, c7_1144_2, c7_1144_3, c7_1144_4, c7_1144_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1111l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1111l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1111l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1111l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1111l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1145_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1111l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1145 :
    hubcapFit theRedpart rf7 p7_1111l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1145_1, c7_1145_2, c7_1145_3, c7_1145_4, c7_1145_5, c7_1145_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1147r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1147r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1147r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1147r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1147r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1148_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1147r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1148 :
    hubcapFit theRedpart rf7 p7_1147r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1148_1, c7_1148_2, c7_1148_3, c7_1148_4, c7_1148_5, c7_1148_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1147l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1147l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1149_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1147l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1149 :
    hubcapFit theRedpart rf7 p7_1147l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1149_1, c7_1149_2, c7_1149_3, c7_1149_4, c7_1149_5, c7_1149_6]

end FourColor

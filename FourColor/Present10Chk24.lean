import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 24 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1088r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1088r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1088r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1089_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1088r) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1089 :
    hubcapFit theRedpart rf10 p10_1088r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1089_1, c10_1089_2, c10_1089_3, c10_1089_4, c10_1089_5, c10_1089_6, c10_1089_7, c10_1089_8, c10_1089_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1088l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1088l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1090_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1088l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1090 :
    hubcapFit theRedpart rf10 p10_1088l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1090_1, c10_1090_2, c10_1090_3, c10_1090_4, c10_1090_5, c10_1090_6, c10_1090_7, c10_1090_8, c10_1090_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1092_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1087l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1092 :
    hubcapFit theRedpart rf10 p10_1087l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1092_1, c10_1092_2, c10_1092_3, c10_1092_4, c10_1092_5, c10_1092_6, c10_1092_7, c10_1092_8, c10_1092_9, c10_1092_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1099r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1099r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1099r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1099r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1099r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1099r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1099r) (hubSubn 10 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1100_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1099r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1100 :
    hubcapFit theRedpart rf10 p10_1099r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1100_1, c10_1100_2, c10_1100_3, c10_1100_4, c10_1100_5, c10_1100_6, c10_1100_7, c10_1100_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1099l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1101_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1099l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1101 :
    hubcapFit theRedpart rf10 p10_1099l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1101_1, c10_1101_2, c10_1101_3, c10_1101_4, c10_1101_5, c10_1101_6, c10_1101_7, c10_1101_8, c10_1101_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1104r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1104r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1104r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1105_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1104r) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1105 :
    hubcapFit theRedpart rf10 p10_1104r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1105_1, c10_1105_2, c10_1105_3, c10_1105_4, c10_1105_5, c10_1105_6, c10_1105_7, c10_1105_8, c10_1105_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1106_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1104l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1106 :
    hubcapFit theRedpart rf10 p10_1104l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1106_1, c10_1106_2, c10_1106_3, c10_1106_4, c10_1106_5, c10_1106_6, c10_1106_7, c10_1106_8, c10_1106_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1108_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1103l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1108 :
    hubcapFit theRedpart rf10 p10_1103l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1108_1, c10_1108_2, c10_1108_3, c10_1108_4, c10_1108_5, c10_1108_6, c10_1108_7, c10_1108_8, c10_1108_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1095l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1095l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1110_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1095l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1110 :
    hubcapFit theRedpart rf10 p10_1095l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1110_1, c10_1110_2, c10_1110_3, c10_1110_4, c10_1110_5, c10_1110_6, c10_1110_7, c10_1110_8, c10_1110_9]

end FourColor

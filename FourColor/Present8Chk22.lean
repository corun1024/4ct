import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 22 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1091l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1091l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1091l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1091l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1091l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1101_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1091l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1101 :
    hubcapFit theRedpart rf8 p8_1091l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1101_1, c8_1101_2, c8_1101_3, c8_1101_4, c8_1101_5, c8_1101_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1069l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1069l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1069l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1069l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1069l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1069l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1103_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1069l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1103 :
    hubcapFit theRedpart rf8 p8_1069l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1103_1, c8_1103_2, c8_1103_3, c8_1103_4, c8_1103_5, c8_1103_6, c8_1103_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1068l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1068l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1105_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1068l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1105 :
    hubcapFit theRedpart rf8 p8_1068l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1105_1, c8_1105_2, c8_1105_3, c8_1105_4, c8_1105_5, c8_1105_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1067l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1067l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1067l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1067l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1067l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1106_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1067l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1106 :
    hubcapFit theRedpart rf8 p8_1067l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1106_1, c8_1106_2, c8_1106_3, c8_1106_4, c8_1106_5, c8_1106_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1066l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1066l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1108_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1066l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1108 :
    hubcapFit theRedpart rf8 p8_1066l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1108_1, c8_1108_2, c8_1108_3, c8_1108_4, c8_1108_5, c8_1108_6, c8_1108_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1051l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1051l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1110_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1051l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1110 :
    hubcapFit theRedpart rf8 p8_1051l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1110_1, c8_1110_2, c8_1110_3, c8_1110_4, c8_1110_5, c8_1110_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1119r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1119r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1119r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1119r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1119r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1120_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1119r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1120 :
    hubcapFit theRedpart rf8 p8_1119r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1120_1, c8_1120_2, c8_1120_3, c8_1120_4, c8_1120_5, c8_1120_6, c8_1120_7, c8_1120_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1119l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1119l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1119l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1119l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1119l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1121_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1119l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1121 :
    hubcapFit theRedpart rf8 p8_1119l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1121_1, c8_1121_2, c8_1121_3, c8_1121_4, c8_1121_5, c8_1121_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1118l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1118l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1123_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1118l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1123 :
    hubcapFit theRedpart rf8 p8_1118l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1123_1, c8_1123_2, c8_1123_3, c8_1123_4, c8_1123_5, c8_1123_6, c8_1123_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1117l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1117l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1117l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1117l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1117l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1117l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1125_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1117l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1125 :
    hubcapFit theRedpart rf8 p8_1117l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1125_1, c8_1125_2, c8_1125_3, c8_1125_4, c8_1125_5, c8_1125_6, c8_1125_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1115l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1115l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1115l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1127_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1115l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1127 :
    hubcapFit theRedpart rf8 p8_1115l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1127_1, c8_1127_2, c8_1127_3, c8_1127_4, c8_1127_5, c8_1127_6, c8_1127_7, c8_1127_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1114l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1114l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1114l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1114l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1114l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1114l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1129_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1114l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1129 :
    hubcapFit theRedpart rf8 p8_1114l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1129_1, c8_1129_2, c8_1129_3, c8_1129_4, c8_1129_5, c8_1129_6, c8_1129_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1113l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1113l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1113l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1113l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1113l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1113l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1131_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1131 :
    hubcapFit theRedpart rf8 p8_1113l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1131_1, c8_1131_2, c8_1131_3, c8_1131_4, c8_1131_5, c8_1131_6, c8_1131_7, c8_1131_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1112l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1112l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1112l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1133_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1112l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1133 :
    hubcapFit theRedpart rf8 p8_1112l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1133_1, c8_1133_2, c8_1133_3, c8_1133_4, c8_1133_5, c8_1133_6, c8_1133_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1142r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1142r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1142r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1142r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1142r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1142r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1143_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1142r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1143 :
    hubcapFit theRedpart rf8 p8_1142r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1143_1, c8_1143_2, c8_1143_3, c8_1143_4, c8_1143_5, c8_1143_6, c8_1143_7]

end FourColor

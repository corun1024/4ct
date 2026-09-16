import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 21 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1057r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1057r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1057r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1057r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1057r) (hubSubn 8 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1058_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1057r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1058 :
    hubcapFit theRedpart rf8 p8_1057r
    (Hubcap.one 3 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1058_1, c8_1058_2, c8_1058_3, c8_1058_4, c8_1058_5, c8_1058_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1057l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1057l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1057l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1059_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1057l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1059 :
    hubcapFit theRedpart rf8 p8_1057l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1059_1, c8_1059_2, c8_1059_3, c8_1059_4, c8_1059_5, c8_1059_6, c8_1059_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1056l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1056l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1056l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1056l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1056l) (hubSubn 8 4 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1061_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1056l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1061 :
    hubcapFit theRedpart rf8 p8_1056l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1061_1, c8_1061_2, c8_1061_3, c8_1061_4, c8_1061_5, c8_1061_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1055l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1055l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1055l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1062_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1055l) (hubSubn 8 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1062 :
    hubcapFit theRedpart rf8 p8_1055l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1062_1, c8_1062_2, c8_1062_3, c8_1062_4, c8_1062_5, c8_1062_6, c8_1062_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1054l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1054l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1054l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1064_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1054l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1064 :
    hubcapFit theRedpart rf8 p8_1054l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1064_1, c8_1064_2, c8_1064_3, c8_1064_4, c8_1064_5, c8_1064_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1078r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1078r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1078r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1078r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1078r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1078r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1079_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1078r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1079 :
    hubcapFit theRedpart rf8 p8_1078r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1079_1, c8_1079_2, c8_1079_3, c8_1079_4, c8_1079_5, c8_1079_6, c8_1079_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1078l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1078l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1078l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1080_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1078l) (hubSubn 8 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1080 :
    hubcapFit theRedpart rf8 p8_1078l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1080_1, c8_1080_2, c8_1080_3, c8_1080_4, c8_1080_5, c8_1080_6, c8_1080_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1077l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1082_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1077l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1082 :
    hubcapFit theRedpart rf8 p8_1077l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1082_1, c8_1082_2, c8_1082_3, c8_1082_4, c8_1082_5, c8_1082_6, c8_1082_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1075l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1075l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1075l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1075l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1075l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1075l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1084_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1075l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1084 :
    hubcapFit theRedpart rf8 p8_1075l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1084_1, c8_1084_2, c8_1084_3, c8_1084_4, c8_1084_5, c8_1084_6, c8_1084_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1074l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1074l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1074l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1074l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1074l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1086_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1074l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1086 :
    hubcapFit theRedpart rf8 p8_1074l
    (Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1086_1, c8_1086_2, c8_1086_3, c8_1086_4, c8_1086_5, c8_1086_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1073l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1073l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1073l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1073l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1073l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1073l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1087_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1073l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1087 :
    hubcapFit theRedpart rf8 p8_1073l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1087_1, c8_1087_2, c8_1087_3, c8_1087_4, c8_1087_5, c8_1087_6, c8_1087_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1072l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1072l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1072l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1089_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1072l) (hubSubn 8 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1089 :
    hubcapFit theRedpart rf8 p8_1072l
    (Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1089_1, c8_1089_2, c8_1089_3, c8_1089_4, c8_1089_5, c8_1089_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1094r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1094r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1094r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1094r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1094r) (hubSubn 8 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1095_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1094r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1095 :
    hubcapFit theRedpart rf8 p8_1094r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1095_1, c8_1095_2, c8_1095_3, c8_1095_4, c8_1095_5, c8_1095_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1094l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1094l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1094l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1094l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1094l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1094l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1096_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1094l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1096 :
    hubcapFit theRedpart rf8 p8_1094l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1096_1, c8_1096_2, c8_1096_3, c8_1096_4, c8_1096_5, c8_1096_6, c8_1096_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1093l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1093l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1093l) (hubSubn 8 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1098_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1093l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1098 :
    hubcapFit theRedpart rf8 p8_1093l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1098_1, c8_1098_2, c8_1098_3, c8_1098_4, c8_1098_5, c8_1098_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1092l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1092l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1092l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1092l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1099_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1092l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1099 :
    hubcapFit theRedpart rf8 p8_1092l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1099_1, c8_1099_2, c8_1099_3, c8_1099_4, c8_1099_5, c8_1099_6, c8_1099_7]

end FourColor

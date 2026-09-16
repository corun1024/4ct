import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 19 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1035l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1035l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1035l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1035l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1035l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1035l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1043_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1035l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1043 :
    hubcapFit theRedpart rf7 p7_1035l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1043_1, c7_1043_2, c7_1043_3, c7_1043_4, c7_1043_5, c7_1043_6, c7_1043_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1029l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1029l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1045_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1029l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1045 :
    hubcapFit theRedpart rf7 p7_1029l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1045_1, c7_1045_2, c7_1045_3, c7_1045_4, c7_1045_5, c7_1045_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1026l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1026l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1026l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1047_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1026l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1047 :
    hubcapFit theRedpart rf7 p7_1026l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1047_1, c7_1047_2, c7_1047_3, c7_1047_4, c7_1047_5, c7_1047_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1049_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1025l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1049_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1025l) (hubSubn 7 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1049_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1025l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1049_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1025l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1049 :
    hubcapFit theRedpart rf7 p7_1025l
    (Hubcap.one 3 (-1) <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1049_1, c7_1049_2, c7_1049_3, c7_1049_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1061_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1060r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1061_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1060r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1061_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1060r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1061_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1060r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1061_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1060r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1061 :
    hubcapFit theRedpart rf7 p7_1060r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1061_1, c7_1061_2, c7_1061_3, c7_1061_4, c7_1061_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1062_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1060l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1062_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1060l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1062_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1060l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1062_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1060l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1062_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1060l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1062 :
    hubcapFit theRedpart rf7 p7_1060l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1062_1, c7_1062_2, c7_1062_3, c7_1062_4, c7_1062_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1059l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1059l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1059l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1059l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1059l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1064_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1059l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1064 :
    hubcapFit theRedpart rf7 p7_1059l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1064_1, c7_1064_2, c7_1064_3, c7_1064_4, c7_1064_5, c7_1064_6, c7_1064_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1066_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1066_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1057l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1066_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1057l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1066_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1057l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1066_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1057l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1066 :
    hubcapFit theRedpart rf7 p7_1057l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1066_1, c7_1066_2, c7_1066_3, c7_1066_4, c7_1066_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1070_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1069r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1070_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1069r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1070_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1069r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1070_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1069r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1070_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1069r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1070 :
    hubcapFit theRedpart rf7 p7_1069r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1070_1, c7_1070_2, c7_1070_3, c7_1070_4, c7_1070_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1069l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1069l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1069l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1069l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1069l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1071_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1069l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1071 :
    hubcapFit theRedpart rf7 p7_1069l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1071_1, c7_1071_2, c7_1071_3, c7_1071_4, c7_1071_5, c7_1071_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1073_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1073_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1068l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1073_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1068l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1073_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1068l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1073_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1068l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1073 :
    hubcapFit theRedpart rf7 p7_1068l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1073_1, c7_1073_2, c7_1073_3, c7_1073_4, c7_1073_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1075_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1055l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1075_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1055l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1075_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1055l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1075_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1055l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1075 :
    hubcapFit theRedpart rf7 p7_1055l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1075_1, c7_1075_2, c7_1075_3, c7_1075_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1080r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1080r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1080r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1080r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1080r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1081_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1080r) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1081 :
    hubcapFit theRedpart rf7 p7_1080r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1081_1, c7_1081_2, c7_1081_3, c7_1081_4, c7_1081_5, c7_1081_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1080l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1080l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1080l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1080l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1082_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1082 :
    hubcapFit theRedpart rf7 p7_1080l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1082_1, c7_1082_2, c7_1082_3, c7_1082_4, c7_1082_5, c7_1082_6, c7_1082_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1084_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1079l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1084_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1079l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1084_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1079l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1084_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1079l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1084_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1079l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1084 :
    hubcapFit theRedpart rf7 p7_1079l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1084_1, c7_1084_2, c7_1084_3, c7_1084_4, c7_1084_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1078l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1078l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1078l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1078l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1078l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1085_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1078l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1085 :
    hubcapFit theRedpart rf7 p7_1078l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1085_1, c7_1085_2, c7_1085_3, c7_1085_4, c7_1085_5, c7_1085_6, c7_1085_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1077l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1077l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1077l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1087_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1077l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1087 :
    hubcapFit theRedpart rf7 p7_1077l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1087_1, c7_1087_2, c7_1087_3, c7_1087_4, c7_1087_5, c7_1087_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1088_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1076l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1088_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1076l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1088_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1076l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1088_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1076l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1088_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1076l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1088 :
    hubcapFit theRedpart rf7 p7_1076l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1088_1, c7_1088_2, c7_1088_3, c7_1088_4, c7_1088_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1091_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1053l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1091_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1053l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1091_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1053l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1091_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1053l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1091_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1053l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1091 :
    hubcapFit theRedpart rf7 p7_1053l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1091_1, c7_1091_2, c7_1091_3, c7_1091_4, c7_1091_5]

end FourColor

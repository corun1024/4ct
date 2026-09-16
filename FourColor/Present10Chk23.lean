import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 23 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1060_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1030l) (hubSubn 10 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1060 :
    hubcapFit theRedpart rf10 p10_1030l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1060_1, c10_1060_2, c10_1060_3, c10_1060_4, c10_1060_5, c10_1060_6, c10_1060_7, c10_1060_8, c10_1060_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1029l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1029l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1029l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1029l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1029l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1029l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1062_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1062 :
    hubcapFit theRedpart rf10 p10_1029l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.one 8 2 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1062_1, c10_1062_2, c10_1062_3, c10_1062_4, c10_1062_5, c10_1062_6, c10_1062_7, c10_1062_8, c10_1062_9, c10_1062_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1028l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1028l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1028l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1028l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1064_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1028l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1064 :
    hubcapFit theRedpart rf10 p10_1028l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1064_1, c10_1064_2, c10_1064_3, c10_1064_4, c10_1064_5, c10_1064_6, c10_1064_7, c10_1064_8, c10_1064_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1026l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1026l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1026l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1026l) (hubSubn 10 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1066_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1026l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1066 :
    hubcapFit theRedpart rf10 p10_1026l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1066_1, c10_1066_2, c10_1066_3, c10_1066_4, c10_1066_5, c10_1066_6, c10_1066_7, c10_1066_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1025l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1025l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1025l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1025l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1025l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1025l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1025l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1068_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1025l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1068 :
    hubcapFit theRedpart rf10 p10_1025l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1068_1, c10_1068_2, c10_1068_3, c10_1068_4, c10_1068_5, c10_1068_6, c10_1068_7, c10_1068_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1024l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1024l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1024l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1024l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1024l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1070_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1024l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1070 :
    hubcapFit theRedpart rf10 p10_1024l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1070_1, c10_1070_2, c10_1070_3, c10_1070_4, c10_1070_5, c10_1070_6, c10_1070_7, c10_1070_8, c10_1070_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1023l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1023l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1023l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1023l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1072_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1023l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1072 :
    hubcapFit theRedpart rf10 p10_1023l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1072_1, c10_1072_2, c10_1072_3, c10_1072_4, c10_1072_5, c10_1072_6, c10_1072_7, c10_1072_8, c10_1072_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1022l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1022l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1022l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1022l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1022l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1022l) (hubSubn 10 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1074_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1022l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1074 :
    hubcapFit theRedpart rf10 p10_1022l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1074_1, c10_1074_2, c10_1074_3, c10_1074_4, c10_1074_5, c10_1074_6, c10_1074_7, c10_1074_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1020l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1020l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1020l) (hubSubn 10 3 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1076_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1020l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1076 :
    hubcapFit theRedpart rf10 p10_1020l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 2 3 9 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1076_1, c10_1076_2, c10_1076_3, c10_1076_4, c10_1076_5, c10_1076_6, c10_1076_7, c10_1076_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1080r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1080r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1080r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1080r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1080r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1081_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1080r) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1081 :
    hubcapFit theRedpart rf10 p10_1080r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1081_1, c10_1081_2, c10_1081_3, c10_1081_4, c10_1081_5, c10_1081_6, c10_1081_7, c10_1081_8, c10_1081_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1080l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1080l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1082_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1080l) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1082 :
    hubcapFit theRedpart rf10 p10_1080l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1082_1, c10_1082_2, c10_1082_3, c10_1082_4, c10_1082_5, c10_1082_6, c10_1082_7, c10_1082_8, c10_1082_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1084r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1084r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1085_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1084r) (hubSubn 10 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1085 :
    hubcapFit theRedpart rf10 p10_1084r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1085_1, c10_1085_2, c10_1085_3, c10_1085_4, c10_1085_5, c10_1085_6, c10_1085_7, c10_1085_8, c10_1085_9]

end FourColor

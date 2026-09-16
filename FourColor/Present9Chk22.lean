import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 22 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1028r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1028r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1028r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1028r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1028r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1028r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1028r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1029_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1028r) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1029 :
    hubcapFit theRedpart rf9 p9_1028r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1029_1, c9_1029_2, c9_1029_3, c9_1029_4, c9_1029_5, c9_1029_6, c9_1029_7, c9_1029_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1041r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1041r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1042_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1041r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1042 :
    hubcapFit theRedpart rf9 p9_1041r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1042_1, c9_1042_2, c9_1042_3, c9_1042_4, c9_1042_5, c9_1042_6, c9_1042_7, c9_1042_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1041l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1041l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1041l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1041l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1041l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1043_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1043 :
    hubcapFit theRedpart rf9 p9_1041l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1043_1, c9_1043_2, c9_1043_3, c9_1043_4, c9_1043_5, c9_1043_6, c9_1043_7, c9_1043_8, c9_1043_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1039l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1039l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1039l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1039l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1039l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1039l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1039l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1039l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1045_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1039l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1045 :
    hubcapFit theRedpart rf9 p9_1039l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1045_1, c9_1045_2, c9_1045_3, c9_1045_4, c9_1045_5, c9_1045_6, c9_1045_7, c9_1045_8, c9_1045_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1037l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1037l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1037l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1037l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1047_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1037l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1047 :
    hubcapFit theRedpart rf9 p9_1037l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1047_1, c9_1047_2, c9_1047_3, c9_1047_4, c9_1047_5, c9_1047_6, c9_1047_7, c9_1047_8, c9_1047_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1036l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1036l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1036l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1036l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1036l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1049_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1036l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1049 :
    hubcapFit theRedpart rf9 p9_1036l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1049_1, c9_1049_2, c9_1049_3, c9_1049_4, c9_1049_5, c9_1049_6, c9_1049_7, c9_1049_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1034l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1034l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1034l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1034l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1034l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1034l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1034l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1034l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1051_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1034l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1051 :
    hubcapFit theRedpart rf9 p9_1034l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1051_1, c9_1051_2, c9_1051_3, c9_1051_4, c9_1051_5, c9_1051_6, c9_1051_7, c9_1051_8, c9_1051_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1031l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1031l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1053_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1031l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1053 :
    hubcapFit theRedpart rf9 p9_1031l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1053_1, c9_1053_2, c9_1053_3, c9_1053_4, c9_1053_5, c9_1053_6, c9_1053_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1023l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1023l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1023l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1023l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1056_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1023l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1056 :
    hubcapFit theRedpart rf9 p9_1023l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1056_1, c9_1056_2, c9_1056_3, c9_1056_4, c9_1056_5, c9_1056_6, c9_1056_7, c9_1056_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1061r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1061r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1061r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1061r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1061r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1061r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1061r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1062_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1061r) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1062 :
    hubcapFit theRedpart rf9 p9_1061r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1062_1, c9_1062_2, c9_1062_3, c9_1062_4, c9_1062_5, c9_1062_6, c9_1062_7, c9_1062_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1059l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1059l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1059l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1059l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1059l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1059l) (hubSubn 9 3 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1064_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1059l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1064 :
    hubcapFit theRedpart rf9 p9_1059l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 8 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1064_1, c9_1064_2, c9_1064_3, c9_1064_4, c9_1064_5, c9_1064_6, c9_1064_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1066l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1066l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1067_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1066l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1067 :
    hubcapFit theRedpart rf9 p9_1066l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1067_1, c9_1067_2, c9_1067_3, c9_1067_4, c9_1067_5, c9_1067_6, c9_1067_7, c9_1067_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1066r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1066r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1066r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1066r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1066r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1066r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1066r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1069_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1066r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1069 :
    hubcapFit theRedpart rf9 p9_1066r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1069_1, c9_1069_2, c9_1069_3, c9_1069_4, c9_1069_5, c9_1069_6, c9_1069_7, c9_1069_8]

end FourColor

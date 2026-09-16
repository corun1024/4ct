import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 22 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_969l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_969l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_969l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_969l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_969l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_969l) (hubSubn 10 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_998_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_969l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_998 :
    hubcapFit theRedpart rf10 p10_969l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_998_1, c10_998_2, c10_998_3, c10_998_4, c10_998_5, c10_998_6, c10_998_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1000r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1000r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1000r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1000r) (hubSubn 10 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1001_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1000r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1001 :
    hubcapFit theRedpart rf10 p10_1000r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1001_1, c10_1001_2, c10_1001_3, c10_1001_4, c10_1001_5, c10_1001_6, c10_1001_7, c10_1001_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1006r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1006r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1006r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1007_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1006r) (hubSubn 10 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1007 :
    hubcapFit theRedpart rf10 p10_1006r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1007_1, c10_1007_2, c10_1007_3, c10_1007_4, c10_1007_5, c10_1007_6, c10_1007_7, c10_1007_8, c10_1007_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1006l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1006l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1006l) (hubSubn 10 5 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1008_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1006l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1008 :
    hubcapFit theRedpart rf10 p10_1006l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1008_1, c10_1008_2, c10_1008_3, c10_1008_4, c10_1008_5, c10_1008_6, c10_1008_7, c10_1008_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1005l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1005l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1010_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1005l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1010 :
    hubcapFit theRedpart rf10 p10_1005l
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
  simp [hubcapFit, c10_1010_1, c10_1010_2, c10_1010_3, c10_1010_4, c10_1010_5, c10_1010_6, c10_1010_7, c10_1010_8, c10_1010_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1012r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1012r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1013_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1012r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1013 :
    hubcapFit theRedpart rf10 p10_1012r
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
  simp [hubcapFit, c10_1013_1, c10_1013_2, c10_1013_3, c10_1013_4, c10_1013_5, c10_1013_6, c10_1013_7, c10_1013_8, c10_1013_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1041r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1041r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1041r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1041r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1041r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1041r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1042_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1041r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1042 :
    hubcapFit theRedpart rf10 p10_1041r
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
  simp [hubcapFit, c10_1042_1, c10_1042_2, c10_1042_3, c10_1042_4, c10_1042_5, c10_1042_6, c10_1042_7, c10_1042_8, c10_1042_9, c10_1042_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1048r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1048r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1048r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1048r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1048r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1048r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1048r) (hubSubn 10 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1049_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1048r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1049 :
    hubcapFit theRedpart rf10 p10_1048r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1049_1, c10_1049_2, c10_1049_3, c10_1049_4, c10_1049_5, c10_1049_6, c10_1049_7, c10_1049_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1048l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1048l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1048l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1048l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1050_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1048l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1050 :
    hubcapFit theRedpart rf10 p10_1048l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1050_1, c10_1050_2, c10_1050_3, c10_1050_4, c10_1050_5, c10_1050_6, c10_1050_7, c10_1050_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1046l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1046l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1046l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1046l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1052_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1046l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1052 :
    hubcapFit theRedpart rf10 p10_1046l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1052_1, c10_1052_2, c10_1052_3, c10_1052_4, c10_1052_5, c10_1052_6, c10_1052_7, c10_1052_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1045l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1045l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1045l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1045l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1054_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1045l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1054 :
    hubcapFit theRedpart rf10 p10_1045l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1054_1, c10_1054_2, c10_1054_3, c10_1054_4, c10_1054_5, c10_1054_6, c10_1054_7, c10_1054_8, c10_1054_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1033l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1033l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1033l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1033l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_1033l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1056_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_1033l) (hubSubn 10 8 7) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1056 :
    hubcapFit theRedpart rf10 p10_1033l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 7 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1056_1, c10_1056_2, c10_1056_3, c10_1056_4, c10_1056_5, c10_1056_6, c10_1056_7, c10_1056_8, c10_1056_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_1031l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_1031l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_1031l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_1031l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_1031l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_1058_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_1031l) (hubSubn 10 9 8) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_1058 :
    hubcapFit theRedpart rf10 p10_1031l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_1058_1, c10_1058_2, c10_1058_3, c10_1058_4, c10_1058_5, c10_1058_6, c10_1058_7, c10_1058_8]

end FourColor

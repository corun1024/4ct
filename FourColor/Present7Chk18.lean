import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 18 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_962l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_962l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_997_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_962l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_997 :
    hubcapFit theRedpart rf7 p7_962l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_997_1, c7_997_2, c7_997_3, c7_997_4, c7_997_5, c7_997_6, c7_997_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_961l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_961l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_961l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_961l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_961l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_999_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_961l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_999 :
    hubcapFit theRedpart rf7 p7_961l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_999_1, c7_999_2, c7_999_3, c7_999_4, c7_999_5, c7_999_6, c7_999_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1005r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1005r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1005r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1005r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1005r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1005r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1006_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1005r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1006 :
    hubcapFit theRedpart rf7 p7_1005r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1006_1, c7_1006_2, c7_1006_3, c7_1006_4, c7_1006_5, c7_1006_6, c7_1006_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1005l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1005l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1005l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1005l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1005l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1005l) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1007_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1005l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1007 :
    hubcapFit theRedpart rf7 p7_1005l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1007_1, c7_1007_2, c7_1007_3, c7_1007_4, c7_1007_5, c7_1007_6, c7_1007_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1004l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1004l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1004l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1004l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1004l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1009_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1004l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1009 :
    hubcapFit theRedpart rf7 p7_1004l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1009_1, c7_1009_2, c7_1009_3, c7_1009_4, c7_1009_5, c7_1009_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1003l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1003l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1003l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1003l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1010_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1003l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1010 :
    hubcapFit theRedpart rf7 p7_1003l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1010_1, c7_1010_2, c7_1010_3, c7_1010_4, c7_1010_5, c7_1010_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1002l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1002l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1002l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1002l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1002l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1012_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1002l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1012 :
    hubcapFit theRedpart rf7 p7_1002l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1012_1, c7_1012_2, c7_1012_3, c7_1012_4, c7_1012_5, c7_1012_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1001l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1001l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1013_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1001l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1013 :
    hubcapFit theRedpart rf7 p7_1001l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1013_1, c7_1013_2, c7_1013_3, c7_1013_4, c7_1013_5, c7_1013_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1019_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1018r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1019_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1018r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1019_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1018r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1019_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1018r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1019_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1018r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1019 :
    hubcapFit theRedpart rf7 p7_1018r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1019_1, c7_1019_2, c7_1019_3, c7_1019_4, c7_1019_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1020_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1018l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1020_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1018l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1020_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1020_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1018l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1020_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1018l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1020 :
    hubcapFit theRedpart rf7 p7_1018l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1020_1, c7_1020_2, c7_1020_3, c7_1020_4, c7_1020_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1017l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1017l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1017l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1017l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1022_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1017l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1022 :
    hubcapFit theRedpart rf7 p7_1017l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1022_1, c7_1022_2, c7_1022_3, c7_1022_4, c7_1022_5, c7_1022_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1031r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1031r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1031r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1031r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1031r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1031r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1032_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1031r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1032 :
    hubcapFit theRedpart rf7 p7_1031r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1032_1, c7_1032_2, c7_1032_3, c7_1032_4, c7_1032_5, c7_1032_6, c7_1032_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1031l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1031l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1033_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1031l) (hubSubn 7 5 4) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1033 :
    hubcapFit theRedpart rf7 p7_1031l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 4 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1033_1, c7_1033_2, c7_1033_3, c7_1033_4, c7_1033_5, c7_1033_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1037r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1037r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1037r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1037r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1037r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1037r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1038_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1037r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1038 :
    hubcapFit theRedpart rf7 p7_1037r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1038_1, c7_1038_2, c7_1038_3, c7_1038_4, c7_1038_5, c7_1038_6, c7_1038_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1037l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1039_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1037l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1039 :
    hubcapFit theRedpart rf7 p7_1037l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1039_1, c7_1039_2, c7_1039_3, c7_1039_4, c7_1039_5, c7_1039_6, c7_1039_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1036l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1036l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1036l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1036l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1036l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1041_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1036l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1041 :
    hubcapFit theRedpart rf7 p7_1036l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1041_1, c7_1041_2, c7_1041_3, c7_1041_4, c7_1041_5, c7_1041_6, c7_1041_7]

end FourColor

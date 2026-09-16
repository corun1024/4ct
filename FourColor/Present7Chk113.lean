import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 113 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6004_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5999l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6004_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5999l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6004_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5999l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6004_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5999l) (hubSubn 7 6 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6004_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5999l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6004 :
    hubcapFit theRedpart rf7 p7_5999l
    (Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 0 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6004_1, c7_6004_2, c7_6004_3, c7_6004_4, c7_6004_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5996l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5996l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6006_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5996l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6006 :
    hubcapFit theRedpart rf7 p7_5996l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6006_1, c7_6006_2, c7_6006_3, c7_6006_4, c7_6006_5, c7_6006_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5995l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5995l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5995l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5995l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6007_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5995l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6007 :
    hubcapFit theRedpart rf7 p7_5995l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6007_1, c7_6007_2, c7_6007_3, c7_6007_4, c7_6007_5, c7_6007_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6015_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6014r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6015_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6014r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6015_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6014r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6015_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6014r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6015_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6014r) (hubSubn 7 6 5) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6015 :
    hubcapFit theRedpart rf7 p7_6014r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6015_1, c7_6015_2, c7_6015_3, c7_6015_4, c7_6015_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6018r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6018r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6018r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6018r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6018r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6019_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6018r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6019 :
    hubcapFit theRedpart rf7 p7_6018r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6019_1, c7_6019_2, c7_6019_3, c7_6019_4, c7_6019_5, c7_6019_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6018l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6018l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6018l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6018l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6018l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6020_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6018l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6020 :
    hubcapFit theRedpart rf7 p7_6018l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6020_1, c7_6020_2, c7_6020_3, c7_6020_4, c7_6020_5, c7_6020_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6017l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6017l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6017l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6017l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6017l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6022_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6017l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6022 :
    hubcapFit theRedpart rf7 p7_6017l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6022_1, c7_6022_2, c7_6022_3, c7_6022_4, c7_6022_5, c7_6022_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6027_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6026r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6027_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6026r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6027_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6026r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6027_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6026r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6027_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6026r) (hubSubn 7 6 5) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6027 :
    hubcapFit theRedpart rf7 p7_6026r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6027_1, c7_6027_2, c7_6027_3, c7_6027_4, c7_6027_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6030r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6030r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6030r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6030r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6030r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6031_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6030r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6031 :
    hubcapFit theRedpart rf7 p7_6030r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-3) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6031_1, c7_6031_2, c7_6031_3, c7_6031_4, c7_6031_5, c7_6031_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6030l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6030l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6030l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6030l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6030l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6032_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6030l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6032 :
    hubcapFit theRedpart rf7 p7_6030l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6032_1, c7_6032_2, c7_6032_3, c7_6032_4, c7_6032_5, c7_6032_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6029l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6029l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6029l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6029l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6029l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6034_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6029l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6034 :
    hubcapFit theRedpart rf7 p7_6029l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 0 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6034_1, c7_6034_2, c7_6034_3, c7_6034_4, c7_6034_5, c7_6034_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6038r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6038r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6038r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6038r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6038r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6039_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_6038r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6039 :
    hubcapFit theRedpart rf7 p7_6038r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-3) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6039_1, c7_6039_2, c7_6039_3, c7_6039_4, c7_6039_5, c7_6039_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6038l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6038l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6038l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6038l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_6038l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6040_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_6038l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6040 :
    hubcapFit theRedpart rf7 p7_6038l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6040_1, c7_6040_2, c7_6040_3, c7_6040_4, c7_6040_5, c7_6040_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6042_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_6037l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6042_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_6037l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6042_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_6037l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6042_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_6037l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_6042_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_6037l) (hubSubn 7 6 5) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_6042 :
    hubcapFit theRedpart rf7 p7_6037l
    (Hubcap.one 1 5 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_6042_1, c7_6042_2, c7_6042_3, c7_6042_4, c7_6042_5]

end FourColor

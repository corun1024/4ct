import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 94 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5004_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5004_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4999l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5004_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4999l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5004_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4999l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5004_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4999l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5004 :
    hubcapFit theRedpart rf7 p7_4999l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5004_1, c7_5004_2, c7_5004_3, c7_5004_4, c7_5004_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4998l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4998l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4998l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4998l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5005_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4998l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5005 :
    hubcapFit theRedpart rf7 p7_4998l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5005_1, c7_5005_2, c7_5005_3, c7_5005_4, c7_5005_5, c7_5005_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5007_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4997l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5007_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4997l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5007_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4997l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5007_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4997l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5007_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4997l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5007 :
    hubcapFit theRedpart rf7 p7_4997l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5007_1, c7_5007_2, c7_5007_3, c7_5007_4, c7_5007_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5008_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5008_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4996l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5008_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4996l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5008_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4996l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5008_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4996l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5008 :
    hubcapFit theRedpart rf7 p7_4996l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5008_1, c7_5008_2, c7_5008_3, c7_5008_4, c7_5008_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5010_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5010_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4995l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5010_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4995l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5010_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4995l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5010_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4995l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5010 :
    hubcapFit theRedpart rf7 p7_4995l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5010_1, c7_5010_2, c7_5010_3, c7_5010_4, c7_5010_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4994l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4994l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4994l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4994l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5011_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4994l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5011 :
    hubcapFit theRedpart rf7 p7_4994l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5011_1, c7_5011_2, c7_5011_3, c7_5011_4, c7_5011_5, c7_5011_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4993l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4993l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4993l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4993l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4993l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5013_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4993l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5013 :
    hubcapFit theRedpart rf7 p7_4993l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5013_1, c7_5013_2, c7_5013_3, c7_5013_4, c7_5013_5, c7_5013_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4992l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4992l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4992l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4992l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5014_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4992l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5014 :
    hubcapFit theRedpart rf7 p7_4992l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5014_1, c7_5014_2, c7_5014_3, c7_5014_4, c7_5014_5, c7_5014_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5018r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5018r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5018r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5018r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5018r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5019_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5018r) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5019 :
    hubcapFit theRedpart rf7 p7_5018r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5019_1, c7_5019_2, c7_5019_3, c7_5019_4, c7_5019_5, c7_5019_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5018l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5018l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5018l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5018l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5020_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5018l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5020 :
    hubcapFit theRedpart rf7 p7_5018l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5020_1, c7_5020_2, c7_5020_3, c7_5020_4, c7_5020_5, c7_5020_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5017l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5017l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5017l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5017l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5022_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5017l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5022 :
    hubcapFit theRedpart rf7 p7_5017l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5022_1, c7_5022_2, c7_5022_3, c7_5022_4, c7_5022_5, c7_5022_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5016l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5016l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5016l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5016l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5023_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5016l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5023 :
    hubcapFit theRedpart rf7 p7_5016l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5023_1, c7_5023_2, c7_5023_3, c7_5023_4, c7_5023_5, c7_5023_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5031r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5031r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5031r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5031r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5031r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5032_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5031r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5032 :
    hubcapFit theRedpart rf7 p7_5031r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5032_1, c7_5032_2, c7_5032_3, c7_5032_4, c7_5032_5, c7_5032_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5033_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5033_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5033_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5031l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5033_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5031l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5033_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5031l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5033 :
    hubcapFit theRedpart rf7 p7_5031l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5033_1, c7_5033_2, c7_5033_3, c7_5033_4, c7_5033_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5030l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5030l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5035_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5030l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5035 :
    hubcapFit theRedpart rf7 p7_5030l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5035_1, c7_5035_2, c7_5035_3, c7_5035_4, c7_5035_5, c7_5035_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5029l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5029l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5029l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5029l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5036_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5029l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5036 :
    hubcapFit theRedpart rf7 p7_5029l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5036_1, c7_5036_2, c7_5036_3, c7_5036_4, c7_5036_5, c7_5036_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5038r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5038r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5038r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5038r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5038r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5038r) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5039_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5038r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5039 :
    hubcapFit theRedpart rf7 p7_5038r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5039_1, c7_5039_2, c7_5039_3, c7_5039_4, c7_5039_5, c7_5039_6, c7_5039_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5038l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5038l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5038l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5038l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5038l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5038l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5040_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5038l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5040 :
    hubcapFit theRedpart rf7 p7_5038l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 2 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5040_1, c7_5040_2, c7_5040_3, c7_5040_4, c7_5040_5, c7_5040_6, c7_5040_7]

end FourColor

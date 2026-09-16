import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 104 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5178l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5178l) (hubSubn 8 5 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5191_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5178l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5191 :
    hubcapFit theRedpart rf8 p8_5178l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 5 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5191_1, c8_5191_2, c8_5191_3, c8_5191_4, c8_5191_5, c8_5191_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5177l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5177l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5177l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5177l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5193_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5177l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5193 :
    hubcapFit theRedpart rf8 p8_5177l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5193_1, c8_5193_2, c8_5193_3, c8_5193_4, c8_5193_5, c8_5193_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5176l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5176l) (hubSubn 8 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5194_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5176l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5194 :
    hubcapFit theRedpart rf8 p8_5176l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5194_1, c8_5194_2, c8_5194_3, c8_5194_4, c8_5194_5, c8_5194_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5206r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5206r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5206r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5206r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5206r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5206r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5206r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5207_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5206r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5207 :
    hubcapFit theRedpart rf8 p8_5206r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5207_1, c8_5207_2, c8_5207_3, c8_5207_4, c8_5207_5, c8_5207_6, c8_5207_7, c8_5207_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5206l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5206l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5208_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5206l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5208 :
    hubcapFit theRedpart rf8 p8_5206l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5208_1, c8_5208_2, c8_5208_3, c8_5208_4, c8_5208_5, c8_5208_6, c8_5208_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5204l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5204l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5204l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5204l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5204l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5204l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5210_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5204l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5210 :
    hubcapFit theRedpart rf8 p8_5204l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5210_1, c8_5210_2, c8_5210_3, c8_5210_4, c8_5210_5, c8_5210_6, c8_5210_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5203l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5203l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5203l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5203l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5203l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5212_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5203l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5212 :
    hubcapFit theRedpart rf8 p8_5203l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5212_1, c8_5212_2, c8_5212_3, c8_5212_4, c8_5212_5, c8_5212_6, c8_5212_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5202l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5202l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5202l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5202l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5202l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5202l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5202l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5214_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5202l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5214 :
    hubcapFit theRedpart rf8 p8_5202l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5214_1, c8_5214_2, c8_5214_3, c8_5214_4, c8_5214_5, c8_5214_6, c8_5214_7, c8_5214_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5219r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5219r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5219r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5219r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5219r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5219r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5220_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5219r) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5220 :
    hubcapFit theRedpart rf8 p8_5219r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5220_1, c8_5220_2, c8_5220_3, c8_5220_4, c8_5220_5, c8_5220_6, c8_5220_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5219l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5219l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5219l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5219l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5219l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5219l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5221_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5219l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5221 :
    hubcapFit theRedpart rf8 p8_5219l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5221_1, c8_5221_2, c8_5221_3, c8_5221_4, c8_5221_5, c8_5221_6, c8_5221_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5217l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5217l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5223_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5217l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5223 :
    hubcapFit theRedpart rf8 p8_5217l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5223_1, c8_5223_2, c8_5223_3, c8_5223_4, c8_5223_5, c8_5223_6, c8_5223_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5216l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5216l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5216l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5216l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5225_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5216l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5225 :
    hubcapFit theRedpart rf8 p8_5216l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5225_1, c8_5225_2, c8_5225_3, c8_5225_4, c8_5225_5, c8_5225_6, c8_5225_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5231r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5231r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5231r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5231r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5231r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5231r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5232_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5231r) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5232 :
    hubcapFit theRedpart rf8 p8_5231r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5232_1, c8_5232_2, c8_5232_3, c8_5232_4, c8_5232_5, c8_5232_6, c8_5232_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5231l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5231l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5231l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5231l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5233_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5231l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5233 :
    hubcapFit theRedpart rf8 p8_5231l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5233_1, c8_5233_2, c8_5233_3, c8_5233_4, c8_5233_5, c8_5233_6, c8_5233_7, c8_5233_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5230l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5230l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5230l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5230l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5230l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5230l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5235_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5235 :
    hubcapFit theRedpart rf8 p8_5230l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5235_1, c8_5235_2, c8_5235_3, c8_5235_4, c8_5235_5, c8_5235_6, c8_5235_7, c8_5235_8]

end FourColor

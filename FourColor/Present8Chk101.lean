import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 101 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5019l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5019l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5019l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5019l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5019l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5031_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5019l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5031 :
    hubcapFit theRedpart rf8 p8_5019l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5031_1, c8_5031_2, c8_5031_3, c8_5031_4, c8_5031_5, c8_5031_6, c8_5031_7, c8_5031_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5051r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5051r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5051r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5051r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5051r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5052_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5051r) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5052 :
    hubcapFit theRedpart rf8 p8_5051r
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5052_1, c8_5052_2, c8_5052_3, c8_5052_4, c8_5052_5, c8_5052_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5051l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5051l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5051l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5051l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5051l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5053_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5051l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5053 :
    hubcapFit theRedpart rf8 p8_5051l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5053_1, c8_5053_2, c8_5053_3, c8_5053_4, c8_5053_5, c8_5053_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5050l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5050l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5050l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5050l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5055_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5050l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5055 :
    hubcapFit theRedpart rf8 p8_5050l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5055_1, c8_5055_2, c8_5055_3, c8_5055_4, c8_5055_5, c8_5055_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5049l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5056_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5049l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5056 :
    hubcapFit theRedpart rf8 p8_5049l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5056_1, c8_5056_2, c8_5056_3, c8_5056_4, c8_5056_5, c8_5056_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5068r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5068r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5068r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5068r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5068r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5068r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5068r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5069_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5068r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5069 :
    hubcapFit theRedpart rf8 p8_5068r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5069_1, c8_5069_2, c8_5069_3, c8_5069_4, c8_5069_5, c8_5069_6, c8_5069_7, c8_5069_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5068l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5068l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5068l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5068l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5068l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5068l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5070_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5068l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5070 :
    hubcapFit theRedpart rf8 p8_5068l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5070_1, c8_5070_2, c8_5070_3, c8_5070_4, c8_5070_5, c8_5070_6, c8_5070_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5067l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5067l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5067l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5067l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5067l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5067l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5072_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5067l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5072 :
    hubcapFit theRedpart rf8 p8_5067l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5072_1, c8_5072_2, c8_5072_3, c8_5072_4, c8_5072_5, c8_5072_6, c8_5072_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5066l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5066l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5066l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5066l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5066l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5066l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5074_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5066l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5074 :
    hubcapFit theRedpart rf8 p8_5066l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5074_1, c8_5074_2, c8_5074_3, c8_5074_4, c8_5074_5, c8_5074_6, c8_5074_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5065l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5065l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5065l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5065l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5065l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5065l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5076_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5065l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5076 :
    hubcapFit theRedpart rf8 p8_5065l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5076_1, c8_5076_2, c8_5076_3, c8_5076_4, c8_5076_5, c8_5076_6, c8_5076_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5064l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5064l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5064l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5064l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5064l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5078_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5064l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5078 :
    hubcapFit theRedpart rf8 p8_5064l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5078_1, c8_5078_2, c8_5078_3, c8_5078_4, c8_5078_5, c8_5078_6, c8_5078_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5063l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5063l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5063l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5063l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5063l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5063l) (hubSubn 8 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5080_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5063l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5080 :
    hubcapFit theRedpart rf8 p8_5063l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5080_1, c8_5080_2, c8_5080_3, c8_5080_4, c8_5080_5, c8_5080_6, c8_5080_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5084r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5084r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5084r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5084r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5084r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5084r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5085_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5084r) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5085 :
    hubcapFit theRedpart rf8 p8_5084r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5085_1, c8_5085_2, c8_5085_3, c8_5085_4, c8_5085_5, c8_5085_6, c8_5085_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5084l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5084l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5084l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5084l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5084l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5086_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5084l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5086 :
    hubcapFit theRedpart rf8 p8_5084l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5086_1, c8_5086_2, c8_5086_3, c8_5086_4, c8_5086_5, c8_5086_6, c8_5086_7, c8_5086_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5083l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5083l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5088_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5083l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5088 :
    hubcapFit theRedpart rf8 p8_5083l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5088_1, c8_5088_2, c8_5088_3, c8_5088_4, c8_5088_5, c8_5088_6, c8_5088_7, c8_5088_8]

end FourColor

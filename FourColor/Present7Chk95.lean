import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 95 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5026l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5026l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5026l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5042_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5026l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5042 :
    hubcapFit theRedpart rf7 p7_5026l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5042_1, c7_5042_2, c7_5042_3, c7_5042_4, c7_5042_5, c7_5042_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5056r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5056r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5056r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5056r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5056r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5056r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5057_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5056r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5057 :
    hubcapFit theRedpart rf7 p7_5056r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5057_1, c7_5057_2, c7_5057_3, c7_5057_4, c7_5057_5, c7_5057_6, c7_5057_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5056l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5056l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5056l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5056l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5056l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5058_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5056l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5058 :
    hubcapFit theRedpart rf7 p7_5056l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5058_1, c7_5058_2, c7_5058_3, c7_5058_4, c7_5058_5, c7_5058_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5055l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5055l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5055l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5055l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5055l) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5060_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5055l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5060 :
    hubcapFit theRedpart rf7 p7_5055l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5060_1, c7_5060_2, c7_5060_3, c7_5060_4, c7_5060_5, c7_5060_6, c7_5060_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5053l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5053l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5053l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5053l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5053l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5062_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5053l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5062 :
    hubcapFit theRedpart rf7 p7_5053l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5062_1, c7_5062_2, c7_5062_3, c7_5062_4, c7_5062_5, c7_5062_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5064_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5052l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5064_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5052l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5064_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5052l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5064_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5052l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5064_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5052l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5064 :
    hubcapFit theRedpart rf7 p7_5052l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 1 <|
     Hubcap.two 2 6 0 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5064_1, c7_5064_2, c7_5064_3, c7_5064_4, c7_5064_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5065_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5051l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5065_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5051l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5065_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5051l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5065_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5051l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5065_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5051l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5065 :
    hubcapFit theRedpart rf7 p7_5051l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5065_1, c7_5065_2, c7_5065_3, c7_5065_4, c7_5065_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5067_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5067_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5067_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5049l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5067_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5049l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5067_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5049l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5067 :
    hubcapFit theRedpart rf7 p7_5049l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5067_1, c7_5067_2, c7_5067_3, c7_5067_4, c7_5067_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5048l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5048l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5048l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5069_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5048l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5069 :
    hubcapFit theRedpart rf7 p7_5048l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5069_1, c7_5069_2, c7_5069_3, c7_5069_4, c7_5069_5, c7_5069_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5047l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5047l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5047l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5047l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5070_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5047l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5070 :
    hubcapFit theRedpart rf7 p7_5047l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5070_1, c7_5070_2, c7_5070_3, c7_5070_4, c7_5070_5, c7_5070_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5072_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5072_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5046l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5072_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5046l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5072_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5046l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5072_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5046l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5072 :
    hubcapFit theRedpart rf7 p7_5046l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5072_1, c7_5072_2, c7_5072_3, c7_5072_4, c7_5072_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5045l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5045l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5045l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5073_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5045l) (hubSubn 7 6 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5073 :
    hubcapFit theRedpart rf7 p7_5045l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5073_1, c7_5073_2, c7_5073_3, c7_5073_4, c7_5073_5, c7_5073_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5088r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5088r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5088r) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5088r) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5088r) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5089_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5088r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5089 :
    hubcapFit theRedpart rf7 p7_5088r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5089_1, c7_5089_2, c7_5089_3, c7_5089_4, c7_5089_5, c7_5089_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5090_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5090_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5088l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5090_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5088l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5090_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5088l) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5090_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5088l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5090 :
    hubcapFit theRedpart rf7 p7_5088l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5090_1, c7_5090_2, c7_5090_3, c7_5090_4, c7_5090_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5092_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5092_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5087l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5092_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5087l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5092_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5087l) (hubSubn 7 6 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5092_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5087l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5092 :
    hubcapFit theRedpart rf7 p7_5087l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5092_1, c7_5092_2, c7_5092_3, c7_5092_4, c7_5092_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5099r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5099r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5099r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5099r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5099r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5100_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5099r) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5100 :
    hubcapFit theRedpart rf7 p7_5099r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5100_1, c7_5100_2, c7_5100_3, c7_5100_4, c7_5100_5, c7_5100_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5099l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5099l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5099l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5099l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5099l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5101_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5099l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5101 :
    hubcapFit theRedpart rf7 p7_5099l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5101_1, c7_5101_2, c7_5101_3, c7_5101_4, c7_5101_5, c7_5101_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5103_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5103_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5103_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5095l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5103_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5095l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5103_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5095l) (hubSubn 7 6 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5103 :
    hubcapFit theRedpart rf7 p7_5095l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5103_1, c7_5103_2, c7_5103_3, c7_5103_4, c7_5103_5]

end FourColor

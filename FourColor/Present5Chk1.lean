import FourColor.Present5Defs
import FourColor.TheQuizTree

/-!
Translated from `present5.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 5 presentation

One of 1 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_6_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_5r) (hubSubn 5 1 0) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_6_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_5r) (hubSubn 5 3 2) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_6_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_5r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_6 :
    hubcapFit theRedpart rf5 p5_5r
    (Hubcap.two 0 1 (-4) <|
     Hubcap.two 2 3 (-4) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_6_1, c5_6_2, c5_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_14_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_13r) (hubSubn 5 1 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_14_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_13r) (hubSubn 5 3 2) (-6)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_14_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_13r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_14 :
    hubcapFit theRedpart rf5 p5_13r
    (Hubcap.two 0 1 (-2) <|
     Hubcap.two 2 3 (-6) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_14_1, c5_14_2, c5_14_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_16_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_15r) (hubSubn 5 1 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_16_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_15r) (hubSubn 5 3 2) (-5)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_16_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_15r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_16 :
    hubcapFit theRedpart rf5 p5_15r
    (Hubcap.two 0 1 (-3) <|
     Hubcap.two 2 3 (-5) <|
     Hubcap.one 4 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_16_1, c5_16_2, c5_16_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_17_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_15l) (hubSubn 5 1 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_17_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_15l) (hubSubn 5 3 2) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_17_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_15l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_17 :
    hubcapFit theRedpart rf5 p5_15l
    (Hubcap.two 0 1 (-3) <|
     Hubcap.two 2 3 (-4) <|
     Hubcap.one 4 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_17_1, c5_17_2, c5_17_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_24_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_23r) (hubSubn 5 1 0) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_24_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_23r) (hubSubn 5 3 2) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_24_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_23r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_24 :
    hubcapFit theRedpart rf5 p5_23r
    (Hubcap.two 0 1 (-4) <|
     Hubcap.two 2 3 (-3) <|
     Hubcap.one 4 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_24_1, c5_24_2, c5_24_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_26_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_25r) (hubSubn 5 1 0) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_26_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_25r) (hubSubn 5 3 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_26_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_25r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_26 :
    hubcapFit theRedpart rf5 p5_25r
    (Hubcap.two 0 1 (-4) <|
     Hubcap.two 2 3 (-2) <|
     Hubcap.one 4 (-4) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_26_1, c5_26_2, c5_26_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_32_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_31r) (hubSubn 5 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_32_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_31r) (hubSubn 5 3 2) (-5)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_32_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_31r) (-5) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_32 :
    hubcapFit theRedpart rf5 p5_31r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 3 (-5) <|
     Hubcap.one 4 (-5) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_32_1, c5_32_2, c5_32_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_33_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_31l) (hubSubn 5 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_33_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_31l) (hubSubn 5 3 2) (-6)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_33_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_31l) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_33 :
    hubcapFit theRedpart rf5 p5_31l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 3 (-6) <|
     Hubcap.one 4 (-4) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_33_1, c5_33_2, c5_33_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_39_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_38l) (hubSubn 5 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_39_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_38l) (hubSubn 5 3 2) (-7)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_39_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_38l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_39 :
    hubcapFit theRedpart rf5 p5_38l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 3 (-7) <|
     Hubcap.one 4 (-3) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_39_1, c5_39_2, c5_39_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_40_1 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 0 p5_37l) (hubSubn 5 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_40_2 :
    check2Dbound2 theRedpart rf5
      (hubcapRot 5 2 p5_37l) (hubSubn 5 3 2) (-6)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c5_40_3 :
    checkDbound2 theRedpart rf5
      (hubcapRot 5 4 p5_37l) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f5_40 :
    hubcapFit theRedpart rf5 p5_37l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 3 (-6) <|
     Hubcap.one 4 (-4) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c5_40_1, c5_40_2, c5_40_3]

end FourColor

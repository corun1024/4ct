import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 109 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5757l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5757l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5757l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5757l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5785_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5757l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5785 :
    hubcapFit theRedpart rf7 p7_5757l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5785_1, c7_5785_2, c7_5785_3, c7_5785_4, c7_5785_5, c7_5785_6, c7_5785_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5788r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5788r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5788r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5788r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5788r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5788r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5789_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5788r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5789 :
    hubcapFit theRedpart rf7 p7_5788r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5789_1, c7_5789_2, c7_5789_3, c7_5789_4, c7_5789_5, c7_5789_6, c7_5789_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5809r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5809r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5809r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5809r) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5809r) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5810_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5809r) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5810 :
    hubcapFit theRedpart rf7 p7_5809r
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5810_1, c7_5810_2, c7_5810_3, c7_5810_4, c7_5810_5, c7_5810_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5812r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5812r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5812r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5812r) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5812r) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5813_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5812r) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5813 :
    hubcapFit theRedpart rf7 p7_5812r
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5813_1, c7_5813_2, c7_5813_3, c7_5813_4, c7_5813_5, c7_5813_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5812l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5812l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5812l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5812l) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5812l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5814_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5812l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5814 :
    hubcapFit theRedpart rf7 p7_5812l
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5814_1, c7_5814_2, c7_5814_3, c7_5814_4, c7_5814_5, c7_5814_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5817r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5817r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5817r) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5817r) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5817r) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5818_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5817r) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5818 :
    hubcapFit theRedpart rf7 p7_5817r
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5818_1, c7_5818_2, c7_5818_3, c7_5818_4, c7_5818_5, c7_5818_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5817l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5817l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5817l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5817l) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5817l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5819_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5817l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5819 :
    hubcapFit theRedpart rf7 p7_5817l
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5819_1, c7_5819_2, c7_5819_3, c7_5819_4, c7_5819_5, c7_5819_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5816l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5816l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5816l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5816l) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5816l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5821_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5816l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5821 :
    hubcapFit theRedpart rf7 p7_5816l
    (Hubcap.one 4 (-2) <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5821_1, c7_5821_2, c7_5821_3, c7_5821_4, c7_5821_5, c7_5821_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5803l) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5803l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5803l) (hubSubn 7 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5803l) (hubSubn 7 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5803l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5823_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5803l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5823 :
    hubcapFit theRedpart rf7 p7_5803l
    (Hubcap.one 4 (-4) <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5823_1, c7_5823_2, c7_5823_3, c7_5823_4, c7_5823_5, c7_5823_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5843r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5843r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5843r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5843r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5843r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5843r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5844_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5843r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5844 :
    hubcapFit theRedpart rf7 p7_5843r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5844_1, c7_5844_2, c7_5844_3, c7_5844_4, c7_5844_5, c7_5844_6, c7_5844_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5843l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5843l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5843l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5843l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5843l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5845_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5843l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5845 :
    hubcapFit theRedpart rf7 p7_5843l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5845_1, c7_5845_2, c7_5845_3, c7_5845_4, c7_5845_5, c7_5845_6, c7_5845_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5842l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5842l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5842l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5847_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5842l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5847 :
    hubcapFit theRedpart rf7 p7_5842l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5847_1, c7_5847_2, c7_5847_3, c7_5847_4, c7_5847_5, c7_5847_6, c7_5847_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5850r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5850r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5850r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5850r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5850r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5850r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5851_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5850r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5851 :
    hubcapFit theRedpart rf7 p7_5850r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5851_1, c7_5851_2, c7_5851_3, c7_5851_4, c7_5851_5, c7_5851_6, c7_5851_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5850l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5850l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5850l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5850l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5850l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5850l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5852_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5850l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5852 :
    hubcapFit theRedpart rf7 p7_5850l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5852_1, c7_5852_2, c7_5852_3, c7_5852_4, c7_5852_5, c7_5852_6, c7_5852_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5849l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5849l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5849l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5849l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5849l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5849l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5854_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5849l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5854 :
    hubcapFit theRedpart rf7 p7_5849l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5854_1, c7_5854_2, c7_5854_3, c7_5854_4, c7_5854_5, c7_5854_6, c7_5854_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5857r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5857r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5857r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5857r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5857r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5857r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5858_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5857r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5858 :
    hubcapFit theRedpart rf7 p7_5857r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5858_1, c7_5858_2, c7_5858_3, c7_5858_4, c7_5858_5, c7_5858_6, c7_5858_7]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 83 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4443l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4449_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4443l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4449 :
    hubcapFit theRedpart rf7 p7_4443l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4449_1, c7_4449_2, c7_4449_3, c7_4449_4, c7_4449_5, c7_4449_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4455_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4454r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4455_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4454r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4455_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4454r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4455_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4454r) (hubSubn 7 4 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4455_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4454r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4455 :
    hubcapFit theRedpart rf7 p7_4454r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4455_1, c7_4455_2, c7_4455_3, c7_4455_4, c7_4455_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4454l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4454l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4454l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4454l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4454l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4454l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4456_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4454l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4456 :
    hubcapFit theRedpart rf7 p7_4454l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4456_1, c7_4456_2, c7_4456_3, c7_4456_4, c7_4456_5, c7_4456_6, c7_4456_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4458_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4458_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4453l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4458_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4453l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4458_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4453l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4458_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4453l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4458 :
    hubcapFit theRedpart rf7 p7_4453l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4458_1, c7_4458_2, c7_4458_3, c7_4458_4, c7_4458_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4452l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4452l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4459_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4452l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4459 :
    hubcapFit theRedpart rf7 p7_4452l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4459_1, c7_4459_2, c7_4459_3, c7_4459_4, c7_4459_5, c7_4459_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4422l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4422l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4422l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4422l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4422l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4462_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4422l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4462 :
    hubcapFit theRedpart rf7 p7_4422l
    (Hubcap.one 0 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4462_1, c7_4462_2, c7_4462_3, c7_4462_4, c7_4462_5, c7_4462_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4463_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4421l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4463_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4421l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4463_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4421l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4463_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4421l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4463_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4421l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4463 :
    hubcapFit theRedpart rf7 p7_4421l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4463_1, c7_4463_2, c7_4463_3, c7_4463_4, c7_4463_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4468r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4468r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4468r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4468r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4468r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4469_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4468r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4469 :
    hubcapFit theRedpart rf7 p7_4468r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4469_1, c7_4469_2, c7_4469_3, c7_4469_4, c7_4469_5, c7_4469_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4468l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4468l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4468l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4468l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4468l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4470_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4468l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4470 :
    hubcapFit theRedpart rf7 p7_4468l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4470_1, c7_4470_2, c7_4470_3, c7_4470_4, c7_4470_5, c7_4470_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4473r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4473r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4473r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4473r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4473r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4474_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4473r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4474 :
    hubcapFit theRedpart rf7 p7_4473r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4474_1, c7_4474_2, c7_4474_3, c7_4474_4, c7_4474_5, c7_4474_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4473l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4473l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4475_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4473l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4475 :
    hubcapFit theRedpart rf7 p7_4473l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4475_1, c7_4475_2, c7_4475_3, c7_4475_4, c7_4475_5, c7_4475_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4472l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4472l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4477_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4477 :
    hubcapFit theRedpart rf7 p7_4472l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4477_1, c7_4477_2, c7_4477_3, c7_4477_4, c7_4477_5, c7_4477_6, c7_4477_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4466l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4466l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4466l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4466l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4466l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4479_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4466l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4479 :
    hubcapFit theRedpart rf7 p7_4466l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4479_1, c7_4479_2, c7_4479_3, c7_4479_4, c7_4479_5, c7_4479_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4465l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4465l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4465l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4465l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4465l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4481_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4481 :
    hubcapFit theRedpart rf7 p7_4465l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4481_1, c7_4481_2, c7_4481_3, c7_4481_4, c7_4481_5, c7_4481_6, c7_4481_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4483_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4419l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4483_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4419l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4483_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4419l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4483_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4419l) (hubSubn 7 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4483_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4419l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4483 :
    hubcapFit theRedpart rf7 p7_4419l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4483_1, c7_4483_2, c7_4483_3, c7_4483_4, c7_4483_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4488r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4488r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4488r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4488r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4488r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4489_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4488r) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4489 :
    hubcapFit theRedpart rf7 p7_4488r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4489_1, c7_4489_2, c7_4489_3, c7_4489_4, c7_4489_5, c7_4489_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4488l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4488l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4490_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4488l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4490 :
    hubcapFit theRedpart rf7 p7_4488l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4490_1, c7_4490_2, c7_4490_3, c7_4490_4, c7_4490_5, c7_4490_6]

end FourColor

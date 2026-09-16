import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 100 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5333r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5333r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5333r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5333r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5333r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5334_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5333r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5334 :
    hubcapFit theRedpart rf7 p7_5333r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5334_1, c7_5334_2, c7_5334_3, c7_5334_4, c7_5334_5, c7_5334_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5333l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5333l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5335_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5333l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5335 :
    hubcapFit theRedpart rf7 p7_5333l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5335_1, c7_5335_2, c7_5335_3, c7_5335_4, c7_5335_5, c7_5335_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5331l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5331l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5337_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5331l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5337 :
    hubcapFit theRedpart rf7 p7_5331l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5337_1, c7_5337_2, c7_5337_3, c7_5337_4, c7_5337_5, c7_5337_6, c7_5337_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5329l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5329l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5329l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5339_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5329l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5339 :
    hubcapFit theRedpart rf7 p7_5329l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5339_1, c7_5339_2, c7_5339_3, c7_5339_4, c7_5339_5, c7_5339_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5328l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5328l) (hubSubn 7 4 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5328l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5341_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5328l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5341 :
    hubcapFit theRedpart rf7 p7_5328l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5341_1, c7_5341_2, c7_5341_3, c7_5341_4, c7_5341_5, c7_5341_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5327l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5327l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5327l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5342_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5327l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5342 :
    hubcapFit theRedpart rf7 p7_5327l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5342_1, c7_5342_2, c7_5342_3, c7_5342_4, c7_5342_5, c7_5342_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5344_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5344_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5344_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5344_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5326l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5344_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5326l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5344 :
    hubcapFit theRedpart rf7 p7_5326l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5344_1, c7_5344_2, c7_5344_3, c7_5344_4, c7_5344_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5345_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5345_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5345_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5345_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5325l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5345_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5325l) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5345 :
    hubcapFit theRedpart rf7 p7_5325l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5345_1, c7_5345_2, c7_5345_3, c7_5345_4, c7_5345_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5351_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5350r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5351_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5350r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5351_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5350r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5351_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5350r) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5351_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5350r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5351 :
    hubcapFit theRedpart rf7 p7_5350r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5351_1, c7_5351_2, c7_5351_3, c7_5351_4, c7_5351_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5350l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5350l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5352_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5350l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5352 :
    hubcapFit theRedpart rf7 p7_5350l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5352_1, c7_5352_2, c7_5352_3, c7_5352_4, c7_5352_5, c7_5352_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5348l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5348l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5354_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5348l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5354 :
    hubcapFit theRedpart rf7 p7_5348l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5354_1, c7_5354_2, c7_5354_3, c7_5354_4, c7_5354_5, c7_5354_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5347l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5347l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5347l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5347l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5347l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5356_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5347l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5356 :
    hubcapFit theRedpart rf7 p7_5347l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-2) <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5356_1, c7_5356_2, c7_5356_3, c7_5356_4, c7_5356_5, c7_5356_6, c7_5356_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5321l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5321l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5321l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5321l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5358_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5321l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5358 :
    hubcapFit theRedpart rf7 p7_5321l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5358_1, c7_5358_2, c7_5358_3, c7_5358_4, c7_5358_5, c7_5358_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5320l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5320l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5320l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5320l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5360_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5320l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5360 :
    hubcapFit theRedpart rf7 p7_5320l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5360_1, c7_5360_2, c7_5360_3, c7_5360_4, c7_5360_5, c7_5360_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5319l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5319l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5319l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5319l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5319l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5361_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5319l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5361 :
    hubcapFit theRedpart rf7 p7_5319l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5361_1, c7_5361_2, c7_5361_3, c7_5361_4, c7_5361_5, c7_5361_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5367r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5367r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5367r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5367r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5367r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5368_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5367r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5368 :
    hubcapFit theRedpart rf7 p7_5367r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5368_1, c7_5368_2, c7_5368_3, c7_5368_4, c7_5368_5, c7_5368_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5373r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5373r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5373r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5373r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5373r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5374_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5373r) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5374 :
    hubcapFit theRedpart rf7 p7_5373r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5374_1, c7_5374_2, c7_5374_3, c7_5374_4, c7_5374_5, c7_5374_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5373l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5373l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5375_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5373l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5375 :
    hubcapFit theRedpart rf7 p7_5373l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5375_1, c7_5375_2, c7_5375_3, c7_5375_4, c7_5375_5, c7_5375_6]

end FourColor

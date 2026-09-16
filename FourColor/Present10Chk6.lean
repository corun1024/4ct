import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_307l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_307l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_307l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_308_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_307l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_308 :
    hubcapFit theRedpart rf10 p10_307l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_308_1, c10_308_2, c10_308_3, c10_308_4, c10_308_5, c10_308_6, c10_308_7, c10_308_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_307r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_307r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_307r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_307r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_310_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_307r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_310 :
    hubcapFit theRedpart rf10 p10_307r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_310_1, c10_310_2, c10_310_3, c10_310_4, c10_310_5, c10_310_6, c10_310_7, c10_310_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_314l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_314l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_314l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_315_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_314l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_315 :
    hubcapFit theRedpart rf10 p10_314l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_315_1, c10_315_2, c10_315_3, c10_315_4, c10_315_5, c10_315_6, c10_315_7, c10_315_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_317l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_317l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_317l) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_318_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_317l) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_318 :
    hubcapFit theRedpart rf10 p10_317l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_318_1, c10_318_2, c10_318_3, c10_318_4, c10_318_5, c10_318_6, c10_318_7, c10_318_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_317r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_317r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_317r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_317r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_317r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_317r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_317r) (hubSubn 10 9 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_320_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_317r) (hubSubn 10 6 4) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_320 :
    hubcapFit theRedpart rf10 p10_317r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 9 9 <|
     Hubcap.two 4 6 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_320_1, c10_320_2, c10_320_3, c10_320_4, c10_320_5, c10_320_6, c10_320_7, c10_320_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_255l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_255l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_255l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_255l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_255l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_255l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_255l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_325_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_255l) (hubSubn 10 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_325 :
    hubcapFit theRedpart rf10 p10_255l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_325_1, c10_325_2, c10_325_3, c10_325_4, c10_325_5, c10_325_6, c10_325_7, c10_325_8, c10_325_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_340r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_340r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_340r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_340r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_340r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_340r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_340r) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_341_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_340r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_341 :
    hubcapFit theRedpart rf10 p10_340r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_341_1, c10_341_2, c10_341_3, c10_341_4, c10_341_5, c10_341_6, c10_341_7, c10_341_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_340l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_340l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_342_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_340l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_342 :
    hubcapFit theRedpart rf10 p10_340l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_342_1, c10_342_2, c10_342_3, c10_342_4, c10_342_5, c10_342_6, c10_342_7, c10_342_8, c10_342_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_339l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_344_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_339l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_344 :
    hubcapFit theRedpart rf10 p10_339l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_344_1, c10_344_2, c10_344_3, c10_344_4, c10_344_5, c10_344_6, c10_344_7, c10_344_8, c10_344_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_338l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_338l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 2 p10_338l) (hubSubn 10 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_346_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_338l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_346 :
    hubcapFit theRedpart rf10 p10_338l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_346_1, c10_346_2, c10_346_3, c10_346_4, c10_346_5, c10_346_6, c10_346_7, c10_346_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_336l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_336l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_348_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_336l) (hubSubn 10 6 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_348 :
    hubcapFit theRedpart rf10 p10_336l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 3 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_348_1, c10_348_2, c10_348_3, c10_348_4, c10_348_5, c10_348_6, c10_348_7, c10_348_8, c10_348_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_335l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_335l) (hubSubn 10 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_350_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 4 p10_335l) (hubSubn 10 9 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_350 :
    hubcapFit theRedpart rf10 p10_335l
    (Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 8 <|
     Hubcap.two 4 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_350_1, c10_350_2, c10_350_3, c10_350_4, c10_350_5, c10_350_6, c10_350_7, c10_350_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_355r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_355r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_355r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_355r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_355r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_355r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_355r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_355r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_356_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_355r) (hubSubn 10 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_356 :
    hubcapFit theRedpart rf10 p10_355r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_356_1, c10_356_2, c10_356_3, c10_356_4, c10_356_5, c10_356_6, c10_356_7, c10_356_8, c10_356_9]

end FourColor

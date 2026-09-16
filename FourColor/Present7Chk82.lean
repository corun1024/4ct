import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 82 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4386l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4386l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4386l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4386l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4391_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4386l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4391 :
    hubcapFit theRedpart rf7 p7_4386l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4391_1, c7_4391_2, c7_4391_3, c7_4391_4, c7_4391_5, c7_4391_6, c7_4391_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4385l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4385l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4385l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4385l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4385l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4385l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4393_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4385l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4393 :
    hubcapFit theRedpart rf7 p7_4385l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4393_1, c7_4393_2, c7_4393_3, c7_4393_4, c7_4393_5, c7_4393_6, c7_4393_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4395r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4395r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4395r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4396_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4395r) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4396 :
    hubcapFit theRedpart rf7 p7_4395r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4396_1, c7_4396_2, c7_4396_3, c7_4396_4, c7_4396_5, c7_4396_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4404r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4404r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4404r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4404r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4404r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4404r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4405_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4404r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4405 :
    hubcapFit theRedpart rf7 p7_4404r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4405_1, c7_4405_2, c7_4405_3, c7_4405_4, c7_4405_5, c7_4405_6, c7_4405_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4404l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4404l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4404l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4404l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4406_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4404l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4406 :
    hubcapFit theRedpart rf7 p7_4404l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4406_1, c7_4406_2, c7_4406_3, c7_4406_4, c7_4406_5, c7_4406_6, c7_4406_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4403l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4403l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4403l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4403l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4403l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4403l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4408_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4403l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4408 :
    hubcapFit theRedpart rf7 p7_4403l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4408_1, c7_4408_2, c7_4408_3, c7_4408_4, c7_4408_5, c7_4408_6, c7_4408_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4402l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4402l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4402l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4402l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4402l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4402l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4410_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4402l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4410 :
    hubcapFit theRedpart rf7 p7_4402l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4410_1, c7_4410_2, c7_4410_3, c7_4410_4, c7_4410_5, c7_4410_6, c7_4410_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4428r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4428r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4428r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4428r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4428r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4429_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4428r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4429 :
    hubcapFit theRedpart rf7 p7_4428r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4429_1, c7_4429_2, c7_4429_3, c7_4429_4, c7_4429_5, c7_4429_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4428l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4428l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4428l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4430_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4428l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4430 :
    hubcapFit theRedpart rf7 p7_4428l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4430_1, c7_4430_2, c7_4430_3, c7_4430_4, c7_4430_5, c7_4430_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4427l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4427l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4427l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4427l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4432_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4427l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4432 :
    hubcapFit theRedpart rf7 p7_4427l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4432_1, c7_4432_2, c7_4432_3, c7_4432_4, c7_4432_5, c7_4432_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4433_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4433_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4433_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4426l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4433_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4426l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4433_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4426l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4433 :
    hubcapFit theRedpart rf7 p7_4426l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4433_1, c7_4433_2, c7_4433_3, c7_4433_4, c7_4433_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4436r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4436r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4436r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4436r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4436r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4436r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4437_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4436r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4437 :
    hubcapFit theRedpart rf7 p7_4436r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4437_1, c7_4437_2, c7_4437_3, c7_4437_4, c7_4437_5, c7_4437_6, c7_4437_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4436l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4436l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4436l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4436l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4436l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4436l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4438_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4436l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4438 :
    hubcapFit theRedpart rf7 p7_4436l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4438_1, c7_4438_2, c7_4438_3, c7_4438_4, c7_4438_5, c7_4438_6, c7_4438_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4435l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4435l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4435l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4435l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4435l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4435l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4440_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4435l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4440 :
    hubcapFit theRedpart rf7 p7_4435l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4440_1, c7_4440_2, c7_4440_3, c7_4440_4, c7_4440_5, c7_4440_6, c7_4440_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4445r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4445r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4445r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4445r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4445r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4446_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4445r) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4446 :
    hubcapFit theRedpart rf7 p7_4445r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4446_1, c7_4446_2, c7_4446_3, c7_4446_4, c7_4446_5, c7_4446_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4445l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4445l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4445l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4447_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4445l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4447 :
    hubcapFit theRedpart rf7 p7_4445l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4447_1, c7_4447_2, c7_4447_3, c7_4447_4, c7_4447_5, c7_4447_6]

end FourColor

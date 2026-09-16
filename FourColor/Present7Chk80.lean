import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 80 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4285l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4285l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4285l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4285l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4287_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4285l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4287 :
    hubcapFit theRedpart rf7 p7_4285l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4287_1, c7_4287_2, c7_4287_3, c7_4287_4, c7_4287_5, c7_4287_6, c7_4287_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4284l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4284l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4284l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4284l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4284l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4289_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4284l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4289 :
    hubcapFit theRedpart rf7 p7_4284l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4289_1, c7_4289_2, c7_4289_3, c7_4289_4, c7_4289_5, c7_4289_6, c7_4289_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4283l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4283l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4283l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4283l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4291_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4283l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4291 :
    hubcapFit theRedpart rf7 p7_4283l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4291_1, c7_4291_2, c7_4291_3, c7_4291_4, c7_4291_5, c7_4291_6, c7_4291_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4281l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4281l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4281l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4293_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4281l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4293 :
    hubcapFit theRedpart rf7 p7_4281l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4293_1, c7_4293_2, c7_4293_3, c7_4293_4, c7_4293_5, c7_4293_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4272l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4272l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4272l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4272l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4296_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4272l) (hubSubn 7 6 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4296 :
    hubcapFit theRedpart rf7 p7_4272l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4296_1, c7_4296_2, c7_4296_3, c7_4296_4, c7_4296_5, c7_4296_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4301r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4301r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4301r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4301r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4301r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4301r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4302_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4301r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4302 :
    hubcapFit theRedpart rf7 p7_4301r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4302_1, c7_4302_2, c7_4302_3, c7_4302_4, c7_4302_5, c7_4302_6, c7_4302_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4315r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4315r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4315r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4315r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4315r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4315r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4316_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4315r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4316 :
    hubcapFit theRedpart rf7 p7_4315r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4316_1, c7_4316_2, c7_4316_3, c7_4316_4, c7_4316_5, c7_4316_6, c7_4316_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4315l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4315l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4315l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4317_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4315l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4317 :
    hubcapFit theRedpart rf7 p7_4315l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4317_1, c7_4317_2, c7_4317_3, c7_4317_4, c7_4317_5, c7_4317_6, c7_4317_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4314l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4314l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4314l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4314l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4314l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4314l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4319_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4314l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4319 :
    hubcapFit theRedpart rf7 p7_4314l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4319_1, c7_4319_2, c7_4319_3, c7_4319_4, c7_4319_5, c7_4319_6, c7_4319_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4323r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4323r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4323r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4323r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4323r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4323r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4324_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4323r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4324 :
    hubcapFit theRedpart rf7 p7_4323r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4324_1, c7_4324_2, c7_4324_3, c7_4324_4, c7_4324_5, c7_4324_6, c7_4324_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4323l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4323l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4323l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4323l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4323l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4325_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4323l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4325 :
    hubcapFit theRedpart rf7 p7_4323l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4325_1, c7_4325_2, c7_4325_3, c7_4325_4, c7_4325_5, c7_4325_6, c7_4325_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4322l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4322l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4322l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4322l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4322l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4322l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4327_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4322l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4327 :
    hubcapFit theRedpart rf7 p7_4322l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4327_1, c7_4327_2, c7_4327_3, c7_4327_4, c7_4327_5, c7_4327_6, c7_4327_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4321l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4321l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4321l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4321l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4321l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4321l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4329_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4321l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4329 :
    hubcapFit theRedpart rf7 p7_4321l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4329_1, c7_4329_2, c7_4329_3, c7_4329_4, c7_4329_5, c7_4329_6, c7_4329_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4336r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4336r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4336r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4336r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4336r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4336r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4337_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4336r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4337 :
    hubcapFit theRedpart rf7 p7_4336r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4337_1, c7_4337_2, c7_4337_3, c7_4337_4, c7_4337_5, c7_4337_6, c7_4337_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4336l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4336l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4336l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4336l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4338_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4336l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4338 :
    hubcapFit theRedpart rf7 p7_4336l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4338_1, c7_4338_2, c7_4338_3, c7_4338_4, c7_4338_5, c7_4338_6, c7_4338_7]

end FourColor

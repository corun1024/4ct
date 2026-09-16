import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 81 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4335l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4335l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4335l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4335l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4340_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4335l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4340 :
    hubcapFit theRedpart rf7 p7_4335l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4340_1, c7_4340_2, c7_4340_3, c7_4340_4, c7_4340_5, c7_4340_6, c7_4340_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4345r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4345r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4345r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4345r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4345r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4345r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4346_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4345r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4346 :
    hubcapFit theRedpart rf7 p7_4345r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4346_1, c7_4346_2, c7_4346_3, c7_4346_4, c7_4346_5, c7_4346_6, c7_4346_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4345l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4345l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4345l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4345l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4345l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4347_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4345l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4347 :
    hubcapFit theRedpart rf7 p7_4345l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4347_1, c7_4347_2, c7_4347_3, c7_4347_4, c7_4347_5, c7_4347_6, c7_4347_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4344l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4344l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4344l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4344l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4344l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4349_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4344l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4349 :
    hubcapFit theRedpart rf7 p7_4344l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4349_1, c7_4349_2, c7_4349_3, c7_4349_4, c7_4349_5, c7_4349_6, c7_4349_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4343l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4343l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4343l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4343l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4343l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4343l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4351_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4343l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4351 :
    hubcapFit theRedpart rf7 p7_4343l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4351_1, c7_4351_2, c7_4351_3, c7_4351_4, c7_4351_5, c7_4351_6, c7_4351_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4342l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4342l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4342l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4342l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4342l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4353_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4342l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4353 :
    hubcapFit theRedpart rf7 p7_4342l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4353_1, c7_4353_2, c7_4353_3, c7_4353_4, c7_4353_5, c7_4353_6, c7_4353_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4357r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4357r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4357r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4357r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4357r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4357r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4358_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4357r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4358 :
    hubcapFit theRedpart rf7 p7_4357r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4358_1, c7_4358_2, c7_4358_3, c7_4358_4, c7_4358_5, c7_4358_6, c7_4358_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4357l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4357l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4357l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4357l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4357l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4357l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4359_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4357l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4359 :
    hubcapFit theRedpart rf7 p7_4357l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4359_1, c7_4359_2, c7_4359_3, c7_4359_4, c7_4359_5, c7_4359_6, c7_4359_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4356l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4356l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4356l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4356l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4356l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4356l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4361_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4356l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4361 :
    hubcapFit theRedpart rf7 p7_4356l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4361_1, c7_4361_2, c7_4361_3, c7_4361_4, c7_4361_5, c7_4361_6, c7_4361_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4355l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4355l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4355l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4355l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4363_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4355l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4363 :
    hubcapFit theRedpart rf7 p7_4355l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4363_1, c7_4363_2, c7_4363_3, c7_4363_4, c7_4363_5, c7_4363_6, c7_4363_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4331l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4331l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4365_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4331l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4365 :
    hubcapFit theRedpart rf7 p7_4331l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4365_1, c7_4365_2, c7_4365_3, c7_4365_4, c7_4365_5, c7_4365_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4367r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4367r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4367r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4367r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4367r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4368_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4367r) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4368 :
    hubcapFit theRedpart rf7 p7_4367r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4368_1, c7_4368_2, c7_4368_3, c7_4368_4, c7_4368_5, c7_4368_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4373r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4373r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4373r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4373r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4373r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4374_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4373r) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4374 :
    hubcapFit theRedpart rf7 p7_4373r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 3 4 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4374_1, c7_4374_2, c7_4374_3, c7_4374_4, c7_4374_5, c7_4374_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4379r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4379r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4379r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4379r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4379r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4379r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4380_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4379r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4380 :
    hubcapFit theRedpart rf7 p7_4379r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4380_1, c7_4380_2, c7_4380_3, c7_4380_4, c7_4380_5, c7_4380_6, c7_4380_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4387r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4387r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4387r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4388_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4387r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4388 :
    hubcapFit theRedpart rf7 p7_4387r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4388_1, c7_4388_2, c7_4388_3, c7_4388_4, c7_4388_5, c7_4388_6, c7_4388_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4387l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4387l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4387l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4387l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4387l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4389_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4387l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4389 :
    hubcapFit theRedpart rf7 p7_4387l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4389_1, c7_4389_2, c7_4389_3, c7_4389_4, c7_4389_5, c7_4389_6, c7_4389_7]

end FourColor

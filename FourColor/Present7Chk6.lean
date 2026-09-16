import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 6 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_363l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_363l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_365_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_363l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_365 :
    hubcapFit theRedpart rf7 p7_363l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_365_1, c7_365_2, c7_365_3, c7_365_4, c7_365_5, c7_365_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_362l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_367_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_362l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_367 :
    hubcapFit theRedpart rf7 p7_362l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_367_1, c7_367_2, c7_367_3, c7_367_4, c7_367_5, c7_367_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_361l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_361l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_361l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_361l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_361l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_368_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_361l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_368 :
    hubcapFit theRedpart rf7 p7_361l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_368_1, c7_368_2, c7_368_3, c7_368_4, c7_368_5, c7_368_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_370_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_360l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_370_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_360l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_370_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_360l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_370_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_360l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_370_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_360l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_370 :
    hubcapFit theRedpart rf7 p7_360l
    (Hubcap.one 1 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_370_1, c7_370_2, c7_370_3, c7_370_4, c7_370_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_359l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_359l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_371_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_371 :
    hubcapFit theRedpart rf7 p7_359l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_371_1, c7_371_2, c7_371_3, c7_371_4, c7_371_5, c7_371_6, c7_371_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_345l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_373_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_345l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_373 :
    hubcapFit theRedpart rf7 p7_345l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_373_1, c7_373_2, c7_373_3, c7_373_4, c7_373_5, c7_373_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_375_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_342l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_375_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_342l) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_375_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_342l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_375_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_342l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_375 :
    hubcapFit theRedpart rf7 p7_342l
    (Hubcap.one 3 2 <|
     Hubcap.two 0 6 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_375_1, c7_375_2, c7_375_3, c7_375_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_383_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_382r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_383_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_382r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_383_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_382r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_383_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_382r) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_383_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_382r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_383 :
    hubcapFit theRedpart rf7 p7_382r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_383_1, c7_383_2, c7_383_3, c7_383_4, c7_383_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_384_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_382l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_384_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_384_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_382l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_384_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_382l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_384_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_382l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_384 :
    hubcapFit theRedpart rf7 p7_382l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_384_1, c7_384_2, c7_384_3, c7_384_4, c7_384_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_386_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_381l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_386_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_381l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_386_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_381l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_386_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_381l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_386 :
    hubcapFit theRedpart rf7 p7_381l
    (Hubcap.one 4 1 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_386_1, c7_386_2, c7_386_3, c7_386_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_387_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_380l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_387_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_380l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_387_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_380l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_387_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_380l) (hubSubn 7 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_387_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_380l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_387 :
    hubcapFit theRedpart rf7 p7_380l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_387_1, c7_387_2, c7_387_3, c7_387_4, c7_387_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_389_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_379l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_389_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_379l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_389_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_379l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_389_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_379l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_389_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_379l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_389 :
    hubcapFit theRedpart rf7 p7_379l
    (Hubcap.two 0 4 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_389_1, c7_389_2, c7_389_3, c7_389_4, c7_389_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_390_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_378l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_390_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_378l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_390_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_378l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_390_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_378l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_390 :
    hubcapFit theRedpart rf7 p7_378l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_390_1, c7_390_2, c7_390_3, c7_390_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_395_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_394r) (hubSubn 7 6 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_395_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_394r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_395_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_394r) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_395_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_394r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_395_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_394r) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_395 :
    hubcapFit theRedpart rf7 p7_394r
    (Hubcap.two 0 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_395_1, c7_395_2, c7_395_3, c7_395_4, c7_395_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_396_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_394l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_396_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_394l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_396_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_394l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_396_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_394l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_396_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_394l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_396 :
    hubcapFit theRedpart rf7 p7_394l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_396_1, c7_396_2, c7_396_3, c7_396_4, c7_396_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_398_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_398_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_393l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_398_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_393l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_398_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_393l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_398_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_393l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_398 :
    hubcapFit theRedpart rf7 p7_393l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_398_1, c7_398_2, c7_398_3, c7_398_4, c7_398_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_400_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_339l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_400_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_339l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_400_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_339l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_400_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_339l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_400 :
    hubcapFit theRedpart rf7 p7_339l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_400_1, c7_400_2, c7_400_3, c7_400_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_405_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_404r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_405_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_404r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_405_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_404r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_405_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_404r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_405_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_404r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_405 :
    hubcapFit theRedpart rf7 p7_404r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_405_1, c7_405_2, c7_405_3, c7_405_4, c7_405_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_407_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_337l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_407_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_337l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_407_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_337l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_407_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_337l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_407 :
    hubcapFit theRedpart rf7 p7_337l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_407_1, c7_407_2, c7_407_3, c7_407_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_418r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_418r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_419_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_418r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_419 :
    hubcapFit theRedpart rf7 p7_418r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_419_1, c7_419_2, c7_419_3, c7_419_4, c7_419_5, c7_419_6]

end FourColor

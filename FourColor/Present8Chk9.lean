import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 9 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_306l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_306l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_306l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_306l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_437_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_306l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_437 :
    hubcapFit theRedpart rf8 p8_306l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_437_1, c8_437_2, c8_437_3, c8_437_4, c8_437_5, c8_437_6, c8_437_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_439_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_130l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_439_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_130l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_439_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_130l) (hubSubn 8 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_439_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_130l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_439_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_130l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_439 :
    hubcapFit theRedpart rf8 p8_130l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_439_1, c8_439_2, c8_439_3, c8_439_4, c8_439_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_441_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_129l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_441_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_129l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_441_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_129l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_441_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_129l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_441_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_129l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_441 :
    hubcapFit theRedpart rf8 p8_129l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_441_1, c8_441_2, c8_441_3, c8_441_4, c8_441_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_463r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_463r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_463r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_463r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_463r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_463r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_464_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_463r) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_464 :
    hubcapFit theRedpart rf8 p8_463r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_464_1, c8_464_2, c8_464_3, c8_464_4, c8_464_5, c8_464_6, c8_464_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_465_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_465_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_465_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_463l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_465_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_463l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_465_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_463l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_465 :
    hubcapFit theRedpart rf8 p8_463l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_465_1, c8_465_2, c8_465_3, c8_465_4, c8_465_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_467_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_467_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_467_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_462l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_467_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_462l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_467_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_462l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_467 :
    hubcapFit theRedpart rf8 p8_462l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_467_1, c8_467_2, c8_467_3, c8_467_4, c8_467_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_468_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_468_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_468_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_461l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_468_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_461l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_468_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_461l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_468 :
    hubcapFit theRedpart rf8 p8_461l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_468_1, c8_468_2, c8_468_3, c8_468_4, c8_468_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_470_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_470_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_459l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_470_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_459l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_470_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_459l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_470_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_459l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_470 :
    hubcapFit theRedpart rf8 p8_459l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_470_1, c8_470_2, c8_470_3, c8_470_4, c8_470_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_458l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_458l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_458l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_458l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_458l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_472_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_458l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_472 :
    hubcapFit theRedpart rf8 p8_458l
    (Hubcap.one 2 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_472_1, c8_472_2, c8_472_3, c8_472_4, c8_472_5, c8_472_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_457l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_457l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_457l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_457l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_457l) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_473_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_457l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_473 :
    hubcapFit theRedpart rf8 p8_457l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_473_1, c8_473_2, c8_473_3, c8_473_4, c8_473_5, c8_473_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_475_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_456l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_475_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_456l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_475_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_456l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_475_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_456l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_475_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_456l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_475 :
    hubcapFit theRedpart rf8 p8_456l
    (Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_475_1, c8_475_2, c8_475_3, c8_475_4, c8_475_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_476_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_455l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_476_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_455l) (hubSubn 8 6 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_476_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_455l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_476_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_455l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_476 :
    hubcapFit theRedpart rf8 p8_455l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_476_1, c8_476_2, c8_476_3, c8_476_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_478_1 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_454l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_478_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_454l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_478_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_454l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_478_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_454l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_478 :
    hubcapFit theRedpart rf8 p8_454l
    (Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_478_1, c8_478_2, c8_478_3, c8_478_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_479_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_453l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_479_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_453l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_479_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_453l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_479_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_453l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_479_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_453l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_479 :
    hubcapFit theRedpart rf8 p8_453l
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_479_1, c8_479_2, c8_479_3, c8_479_4, c8_479_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_452l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_452l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_452l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_452l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_481_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_452l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_481 :
    hubcapFit theRedpart rf8 p8_452l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_481_1, c8_481_2, c8_481_3, c8_481_4, c8_481_5, c8_481_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_497r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_497r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_497r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_497r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_497r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_497r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_498_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_497r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_498 :
    hubcapFit theRedpart rf8 p8_497r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_498_1, c8_498_2, c8_498_3, c8_498_4, c8_498_5, c8_498_6, c8_498_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_497l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_497l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_497l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_497l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_499_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_497l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_499 :
    hubcapFit theRedpart rf8 p8_497l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_499_1, c8_499_2, c8_499_3, c8_499_4, c8_499_5, c8_499_6, c8_499_7, c8_499_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_495l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_495l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_501_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_495l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_501 :
    hubcapFit theRedpart rf8 p8_495l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_501_1, c8_501_2, c8_501_3, c8_501_4, c8_501_5, c8_501_6, c8_501_7]

end FourColor

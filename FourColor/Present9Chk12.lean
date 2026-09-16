import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 12 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_530r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_530r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_530r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_530r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_530r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_530r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_530r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_530r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_531_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_530r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_531 :
    hubcapFit theRedpart rf9 p9_530r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_531_1, c9_531_2, c9_531_3, c9_531_4, c9_531_5, c9_531_6, c9_531_7, c9_531_8, c9_531_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_532_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_532 :
    hubcapFit theRedpart rf9 p9_530l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_532_1, c9_532_2, c9_532_3, c9_532_4, c9_532_5, c9_532_6, c9_532_7, c9_532_8, c9_532_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_528l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_534_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_528l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_534 :
    hubcapFit theRedpart rf9 p9_528l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_534_1, c9_534_2, c9_534_3, c9_534_4, c9_534_5, c9_534_6, c9_534_7, c9_534_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_527l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_536_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_527l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_536 :
    hubcapFit theRedpart rf9 p9_527l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_536_1, c9_536_2, c9_536_3, c9_536_4, c9_536_5, c9_536_6, c9_536_7, c9_536_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_526l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_526l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_538_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_526l) (hubSubn 9 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_538 :
    hubcapFit theRedpart rf9 p9_526l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_538_1, c9_538_2, c9_538_3, c9_538_4, c9_538_5, c9_538_6, c9_538_7, c9_538_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_525l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_525l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_525l) (hubSubn 9 8 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_525l) (hubSubn 9 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_540_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_525l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_540 :
    hubcapFit theRedpart rf9 p9_525l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 1 8 5 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_540_1, c9_540_2, c9_540_3, c9_540_4, c9_540_5, c9_540_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_523l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_523l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_523l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_523l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_523l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_542_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_523l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_542 :
    hubcapFit theRedpart rf9 p9_523l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_542_1, c9_542_2, c9_542_3, c9_542_4, c9_542_5, c9_542_6, c9_542_7, c9_542_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_544_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_498l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_544_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_498l) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_544_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_498l) (hubSubn 9 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_544_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_498l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_544_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_498l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_544 :
    hubcapFit theRedpart rf9 p9_498l
    (Hubcap.one 0 4 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_544_1, c9_544_2, c9_544_3, c9_544_4, c9_544_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_546_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_497l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_546_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_497l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_546_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_497l) (hubSubn 9 4 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_546_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_497l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_546_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_497l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_546 :
    hubcapFit theRedpart rf9 p9_497l
    (Hubcap.one 3 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 4 8 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_546_1, c9_546_2, c9_546_3, c9_546_4, c9_546_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_496l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_496l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_496l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_496l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_496l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_496l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_547_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_496l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_547 :
    hubcapFit theRedpart rf9 p9_496l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_547_1, c9_547_2, c9_547_3, c9_547_4, c9_547_5, c9_547_6, c9_547_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_495l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_495l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_495l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_495l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_495l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_549_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_495l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_549 :
    hubcapFit theRedpart rf9 p9_495l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_549_1, c9_549_2, c9_549_3, c9_549_4, c9_549_5, c9_549_6, c9_549_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_361l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_361l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_361l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_361l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_361l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_361l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_552_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_361l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_552 :
    hubcapFit theRedpart rf9 p9_361l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_552_1, c9_552_2, c9_552_3, c9_552_4, c9_552_5, c9_552_6, c9_552_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_345l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_345l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_345l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_345l) (hubSubn 9 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_345l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_554_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_345l) (hubSubn 9 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_554 :
    hubcapFit theRedpart rf9 p9_345l
    (Hubcap.one 0 5 <|
     Hubcap.one 7 0 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_554_1, c9_554_2, c9_554_3, c9_554_4, c9_554_5, c9_554_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_344l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_344l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_344l) (hubSubn 9 3 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_344l) (hubSubn 9 4 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_556_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_344l) (hubSubn 9 8 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_556 :
    hubcapFit theRedpart rf9 p9_344l
    (Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 8 <|
     Hubcap.two 1 4 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_556_1, c9_556_2, c9_556_3, c9_556_4, c9_556_5, c9_556_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_582r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_582r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_582r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_582r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_582r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_582r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_583_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_582r) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_583 :
    hubcapFit theRedpart rf9 p9_582r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_583_1, c9_583_2, c9_583_3, c9_583_4, c9_583_5, c9_583_6, c9_583_7, c9_583_8]

end FourColor

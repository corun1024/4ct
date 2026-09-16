import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 106 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5279l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5279l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5279l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5279l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5279l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5287_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5279l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5287 :
    hubcapFit theRedpart rf8 p8_5279l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5287_1, c8_5287_2, c8_5287_3, c8_5287_4, c8_5287_5, c8_5287_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5255l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5255l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5255l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5255l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5255l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5255l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5255l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5289_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5255l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5289 :
    hubcapFit theRedpart rf8 p8_5255l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5289_1, c8_5289_2, c8_5289_3, c8_5289_4, c8_5289_5, c8_5289_6, c8_5289_7, c8_5289_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5254l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5254l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5254l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5254l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5254l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5291_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5254l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5291 :
    hubcapFit theRedpart rf8 p8_5254l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5291_1, c8_5291_2, c8_5291_3, c8_5291_4, c8_5291_5, c8_5291_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5293r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5293r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5293r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5293r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5293r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5293r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5294_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5293r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5294 :
    hubcapFit theRedpart rf8 p8_5293r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5294_1, c8_5294_2, c8_5294_3, c8_5294_4, c8_5294_5, c8_5294_6, c8_5294_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5302r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5302r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5302r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5302r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5302r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5303_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5302r) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5303 :
    hubcapFit theRedpart rf8 p8_5302r
    (Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5303_1, c8_5303_2, c8_5303_3, c8_5303_4, c8_5303_5, c8_5303_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5302l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5302l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5302l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5302l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5302l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5302l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5304_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5302l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5304 :
    hubcapFit theRedpart rf8 p8_5302l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5304_1, c8_5304_2, c8_5304_3, c8_5304_4, c8_5304_5, c8_5304_6, c8_5304_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5301l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5301l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5301l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5301l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5301l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5301l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5306_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5301l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5306 :
    hubcapFit theRedpart rf8 p8_5301l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5306_1, c8_5306_2, c8_5306_3, c8_5306_4, c8_5306_5, c8_5306_6, c8_5306_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5308_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5300l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5308_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5300l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5308_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5300l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5308_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5300l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5308_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5300l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5308 :
    hubcapFit theRedpart rf8 p8_5300l
    (Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5308_1, c8_5308_2, c8_5308_3, c8_5308_4, c8_5308_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5310r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5310r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5310r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5310r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5310r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5310r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5311_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5310r) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5311 :
    hubcapFit theRedpart rf8 p8_5310r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5311_1, c8_5311_2, c8_5311_3, c8_5311_4, c8_5311_5, c8_5311_6, c8_5311_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5312_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5310l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5312_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5310l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5312_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5310l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5312_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5310l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5312_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5310l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5312 :
    hubcapFit theRedpart rf8 p8_5310l
    (Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5312_1, c8_5312_2, c8_5312_3, c8_5312_4, c8_5312_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5298l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5298l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5298l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5298l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5298l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5315_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5298l) (hubSubn 8 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5315 :
    hubcapFit theRedpart rf8 p8_5298l
    (Hubcap.one 0 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5315_1, c8_5315_2, c8_5315_3, c8_5315_4, c8_5315_5, c8_5315_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5332r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5332r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5332r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5332r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5332r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5332r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5332r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5333_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5332r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5333 :
    hubcapFit theRedpart rf8 p8_5332r
    (Hubcap.one 0 (-2) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5333_1, c8_5333_2, c8_5333_3, c8_5333_4, c8_5333_5, c8_5333_6, c8_5333_7, c8_5333_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5332l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5332l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5332l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5334_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5332l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5334 :
    hubcapFit theRedpart rf8 p8_5332l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5334_1, c8_5334_2, c8_5334_3, c8_5334_4, c8_5334_5, c8_5334_6, c8_5334_7, c8_5334_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5331l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5331l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5331l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5331l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5336_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5336 :
    hubcapFit theRedpart rf8 p8_5331l
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5336_1, c8_5336_2, c8_5336_3, c8_5336_4, c8_5336_5, c8_5336_6, c8_5336_7, c8_5336_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5339r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5339r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5339r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5339r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5339r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5339r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5339r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5340_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5339r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5340 :
    hubcapFit theRedpart rf8 p8_5339r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5340_1, c8_5340_2, c8_5340_3, c8_5340_4, c8_5340_5, c8_5340_6, c8_5340_7, c8_5340_8]

end FourColor

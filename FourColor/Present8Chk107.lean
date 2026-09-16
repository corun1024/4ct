import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 107 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5339l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5339l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5339l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5339l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5341_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5339l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5341 :
    hubcapFit theRedpart rf8 p8_5339l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5341_1, c8_5341_2, c8_5341_3, c8_5341_4, c8_5341_5, c8_5341_6, c8_5341_7, c8_5341_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5338l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5338l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5338l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5338l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5343_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5338l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5343 :
    hubcapFit theRedpart rf8 p8_5338l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5343_1, c8_5343_2, c8_5343_3, c8_5343_4, c8_5343_5, c8_5343_6, c8_5343_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5350r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5350r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5350r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5350r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5350r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5350r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5350r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5351_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5350r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5351 :
    hubcapFit theRedpart rf8 p8_5350r
    (Hubcap.one 0 (-1) <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5351_1, c8_5351_2, c8_5351_3, c8_5351_4, c8_5351_5, c8_5351_6, c8_5351_7, c8_5351_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5350l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5350l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5350l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5350l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5352_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5352 :
    hubcapFit theRedpart rf8 p8_5350l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5352_1, c8_5352_2, c8_5352_3, c8_5352_4, c8_5352_5, c8_5352_6, c8_5352_7, c8_5352_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5347l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5347l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5347l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5347l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5347l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5354_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5347l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5354 :
    hubcapFit theRedpart rf8 p8_5347l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5354_1, c8_5354_2, c8_5354_3, c8_5354_4, c8_5354_5, c8_5354_6, c8_5354_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5346l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5346l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5346l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5346l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5346l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5346l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5356_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5356 :
    hubcapFit theRedpart rf8 p8_5346l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5356_1, c8_5356_2, c8_5356_3, c8_5356_4, c8_5356_5, c8_5356_6, c8_5356_7, c8_5356_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5345l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5345l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5345l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5345l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5345l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5345l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5358_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5345l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5358 :
    hubcapFit theRedpart rf8 p8_5345l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5358_1, c8_5358_2, c8_5358_3, c8_5358_4, c8_5358_5, c8_5358_6, c8_5358_7, c8_5358_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5327l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5327l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5327l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5327l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5327l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5327l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5360_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5360 :
    hubcapFit theRedpart rf8 p8_5327l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5360_1, c8_5360_2, c8_5360_3, c8_5360_4, c8_5360_5, c8_5360_6, c8_5360_7, c8_5360_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5326l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5326l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5326l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5362_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5362 :
    hubcapFit theRedpart rf8 p8_5326l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5362_1, c8_5362_2, c8_5362_3, c8_5362_4, c8_5362_5, c8_5362_6, c8_5362_7, c8_5362_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5380r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5380r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5380r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5380r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5380r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5380r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5380r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5381_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5380r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5381 :
    hubcapFit theRedpart rf8 p8_5380r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5381_1, c8_5381_2, c8_5381_3, c8_5381_4, c8_5381_5, c8_5381_6, c8_5381_7, c8_5381_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5383r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5383r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5383r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5383r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5383r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5383r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5383r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5384_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5383r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5384 :
    hubcapFit theRedpart rf8 p8_5383r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5384_1, c8_5384_2, c8_5384_3, c8_5384_4, c8_5384_5, c8_5384_6, c8_5384_7, c8_5384_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5383l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5383l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5383l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5383l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5383l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5383l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5385_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5383l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5385 :
    hubcapFit theRedpart rf8 p8_5383l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5385_1, c8_5385_2, c8_5385_3, c8_5385_4, c8_5385_5, c8_5385_6, c8_5385_7, c8_5385_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5389r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5389r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5389r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5389r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5389r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5389r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5389r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5390_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5389r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5390 :
    hubcapFit theRedpart rf8 p8_5389r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5390_1, c8_5390_2, c8_5390_3, c8_5390_4, c8_5390_5, c8_5390_6, c8_5390_7, c8_5390_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_5389l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_5389l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_5389l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_5389l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_5389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_5389l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_5389l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_5391_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_5389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_5391 :
    hubcapFit theRedpart rf8 p8_5389l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_5391_1, c8_5391_2, c8_5391_3, c8_5391_4, c8_5391_5, c8_5391_6, c8_5391_7, c8_5391_8]

end FourColor

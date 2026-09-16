import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 7 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_339l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_339l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_339l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_354_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_339l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_354 :
    hubcapFit theRedpart rf8 p8_339l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_354_1, c8_354_2, c8_354_3, c8_354_4, c8_354_5, c8_354_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_356_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_338l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_356_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_338l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_356_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_338l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_356_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_338l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_356_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_338l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_356 :
    hubcapFit theRedpart rf8 p8_338l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_356_1, c8_356_2, c8_356_3, c8_356_4, c8_356_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_357_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_337l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_357_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_337l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_357_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_337l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_357_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_337l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_357_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_337l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_357 :
    hubcapFit theRedpart rf8 p8_337l
    (Hubcap.one 2 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_357_1, c8_357_2, c8_357_3, c8_357_4, c8_357_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_359_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_336l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_359_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_336l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_359_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_336l) (hubSubn 8 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_359_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_336l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_359_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_336l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_359 :
    hubcapFit theRedpart rf8 p8_336l
    (Hubcap.one 3 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_359_1, c8_359_2, c8_359_3, c8_359_4, c8_359_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_335l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_335l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_335l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_335l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_335l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_360_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_335l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_360 :
    hubcapFit theRedpart rf8 p8_335l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_360_1, c8_360_2, c8_360_3, c8_360_4, c8_360_5, c8_360_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_362_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_315l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_362_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_315l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_362_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_315l) (hubSubn 8 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_362_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_315l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_362_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_315l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_362 :
    hubcapFit theRedpart rf8 p8_315l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_362_1, c8_362_2, c8_362_3, c8_362_4, c8_362_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_364_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_313l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_364_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_313l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_364_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_313l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_364_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_313l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_364_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_313l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_364 :
    hubcapFit theRedpart rf8 p8_313l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_364_1, c8_364_2, c8_364_3, c8_364_4, c8_364_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_312l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_312l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_312l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_312l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_366_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_312l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_366 :
    hubcapFit theRedpart rf8 p8_312l
    (Hubcap.one 0 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_366_1, c8_366_2, c8_366_3, c8_366_4, c8_366_5, c8_366_6, c8_366_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_311l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_311l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_311l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_311l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_311l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_368_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_311l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_368 :
    hubcapFit theRedpart rf8 p8_311l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_368_1, c8_368_2, c8_368_3, c8_368_4, c8_368_5, c8_368_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_369_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_310l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_369_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_310l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_369_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_310l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_369_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_310l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_369_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_310l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_369 :
    hubcapFit theRedpart rf8 p8_310l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_369_1, c8_369_2, c8_369_3, c8_369_4, c8_369_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_371_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_309l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_371_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_309l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_371_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_309l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_371_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_309l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_371_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_309l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_371 :
    hubcapFit theRedpart rf8 p8_309l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_371_1, c8_371_2, c8_371_3, c8_371_4, c8_371_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_390r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_390r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_391_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_390r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_391 :
    hubcapFit theRedpart rf8 p8_390r
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_391_1, c8_391_2, c8_391_3, c8_391_4, c8_391_5, c8_391_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_390l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_392_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_390l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_392 :
    hubcapFit theRedpart rf8 p8_390l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_392_1, c8_392_2, c8_392_3, c8_392_4, c8_392_5, c8_392_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_389l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_389l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_389l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_394_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_389l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_394 :
    hubcapFit theRedpart rf8 p8_389l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_394_1, c8_394_2, c8_394_3, c8_394_4, c8_394_5, c8_394_6, c8_394_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_388l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_388l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_396_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_388l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_396 :
    hubcapFit theRedpart rf8 p8_388l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_396_1, c8_396_2, c8_396_3, c8_396_4, c8_396_5, c8_396_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_387l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_397_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_387l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_397 :
    hubcapFit theRedpart rf8 p8_387l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_397_1, c8_397_2, c8_397_3, c8_397_4, c8_397_5, c8_397_6, c8_397_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_399_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_399_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_399_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_386l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_399_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_386l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_399_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_386l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_399 :
    hubcapFit theRedpart rf8 p8_386l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_399_1, c8_399_2, c8_399_3, c8_399_4, c8_399_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_401_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_384l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_401_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_384l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_401_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_384l) (hubSubn 8 4 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_401_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_384l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_401_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_384l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_401 :
    hubcapFit theRedpart rf8 p8_384l
    (Hubcap.one 3 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_401_1, c8_401_2, c8_401_3, c8_401_4, c8_401_5]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 8 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_351l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_351l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_351l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_353_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_353 :
    hubcapFit theRedpart rf9 p9_351l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_353_1, c9_353_2, c9_353_3, c9_353_4, c9_353_5, c9_353_6, c9_353_7, c9_353_8, c9_353_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_350l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_355_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_350l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_355 :
    hubcapFit theRedpart rf9 p9_350l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 2 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_355_1, c9_355_2, c9_355_3, c9_355_4, c9_355_5, c9_355_6, c9_355_7, c9_355_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_349l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_349l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_349l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_357_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_349l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_357 :
    hubcapFit theRedpart rf9 p9_349l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_357_1, c9_357_2, c9_357_3, c9_357_4, c9_357_5, c9_357_6, c9_357_7, c9_357_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_359_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_359 :
    hubcapFit theRedpart rf9 p9_348l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_359_1, c9_359_2, c9_359_3, c9_359_4, c9_359_5, c9_359_6, c9_359_7, c9_359_8, c9_359_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_378r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_378r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_378r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_378r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_378r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_378r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_378r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_378r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_379_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_378r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_379 :
    hubcapFit theRedpart rf9 p9_378r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_379_1, c9_379_2, c9_379_3, c9_379_4, c9_379_5, c9_379_6, c9_379_7, c9_379_8, c9_379_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_378l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_378l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_380_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_378l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_380 :
    hubcapFit theRedpart rf9 p9_378l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_380_1, c9_380_2, c9_380_3, c9_380_4, c9_380_5, c9_380_6, c9_380_7, c9_380_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_377l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_377l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_377l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_382_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_377l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_382 :
    hubcapFit theRedpart rf9 p9_377l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_382_1, c9_382_2, c9_382_3, c9_382_4, c9_382_5, c9_382_6, c9_382_7, c9_382_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_384_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_375l) (hubSubn 9 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_384 :
    hubcapFit theRedpart rf9 p9_375l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_384_1, c9_384_2, c9_384_3, c9_384_4, c9_384_5, c9_384_6, c9_384_7, c9_384_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_374l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_386_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_374l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_386 :
    hubcapFit theRedpart rf9 p9_374l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_386_1, c9_386_2, c9_386_3, c9_386_4, c9_386_5, c9_386_6, c9_386_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_373l) (hubSubn 9 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_388_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_373l) (hubSubn 9 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_388 :
    hubcapFit theRedpart rf9 p9_373l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 5 7 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_388_1, c9_388_2, c9_388_3, c9_388_4, c9_388_5, c9_388_6, c9_388_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_390r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_390r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_390r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_390r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_391_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_390r) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_391 :
    hubcapFit theRedpart rf9 p9_390r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_391_1, c9_391_2, c9_391_3, c9_391_4, c9_391_5, c9_391_6, c9_391_7, c9_391_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_390l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_390l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_390l) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_392_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_390l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_392 :
    hubcapFit theRedpart rf9 p9_390l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_392_1, c9_392_2, c9_392_3, c9_392_4, c9_392_5, c9_392_6, c9_392_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_395r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_395r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_395r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_395r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_396_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_395r) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_396 :
    hubcapFit theRedpart rf9 p9_395r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_396_1, c9_396_2, c9_396_3, c9_396_4, c9_396_5, c9_396_6, c9_396_7, c9_396_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_395l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_395l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_395l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_395l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_395l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_395l) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_397_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_395l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_397 :
    hubcapFit theRedpart rf9 p9_395l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_397_1, c9_397_2, c9_397_3, c9_397_4, c9_397_5, c9_397_6, c9_397_7]

end FourColor

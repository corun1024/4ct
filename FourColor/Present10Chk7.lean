import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 7 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_355l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_355l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_357_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_355l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_357 :
    hubcapFit theRedpart rf10 p10_355l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_357_1, c10_357_2, c10_357_3, c10_357_4, c10_357_5, c10_357_6, c10_357_7, c10_357_8, c10_357_9, c10_357_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_354l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_354l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_354l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_354l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_360_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_354l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_360 :
    hubcapFit theRedpart rf10 p10_354l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_360_1, c10_360_2, c10_360_3, c10_360_4, c10_360_5, c10_360_6, c10_360_7, c10_360_8, c10_360_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_333l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_333l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_333l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_362_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_333l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_362 :
    hubcapFit theRedpart rf10 p10_333l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_362_1, c10_362_2, c10_362_3, c10_362_4, c10_362_5, c10_362_6, c10_362_7, c10_362_8, c10_362_9, c10_362_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_332l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_332l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_332l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_332l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_365_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_332l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_365 :
    hubcapFit theRedpart rf10 p10_332l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_365_1, c10_365_2, c10_365_3, c10_365_4, c10_365_5, c10_365_6, c10_365_7, c10_365_8, c10_365_9, c10_365_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_331l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_331l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_331l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_331l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_367_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_331l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_367 :
    hubcapFit theRedpart rf10 p10_331l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_367_1, c10_367_2, c10_367_3, c10_367_4, c10_367_5, c10_367_6, c10_367_7, c10_367_8, c10_367_9, c10_367_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_377r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_377r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_377r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_377r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_377r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_377r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_377r) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_378_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_377r) (hubSubn 10 9 7) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_378 :
    hubcapFit theRedpart rf10 p10_377r
    (Hubcap.one 1 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 7 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_378_1, c10_378_2, c10_378_3, c10_378_4, c10_378_5, c10_378_6, c10_378_7, c10_378_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_377l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_379_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_377l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_379 :
    hubcapFit theRedpart rf10 p10_377l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_379_1, c10_379_2, c10_379_3, c10_379_4, c10_379_5, c10_379_6, c10_379_7, c10_379_8, c10_379_9, c10_379_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_376l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_382_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_376l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_382 :
    hubcapFit theRedpart rf10 p10_376l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_382_1, c10_382_2, c10_382_3, c10_382_4, c10_382_5, c10_382_6, c10_382_7, c10_382_8, c10_382_9, c10_382_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_384_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_384 :
    hubcapFit theRedpart rf10 p10_375l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_384_1, c10_384_2, c10_384_3, c10_384_4, c10_384_5, c10_384_6, c10_384_7, c10_384_8, c10_384_9, c10_384_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_374l) (hubSubn 10 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_374l) (hubSubn 10 3 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_386_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_374l) (hubSubn 10 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_386 :
    hubcapFit theRedpart rf10 p10_374l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 9 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_386_1, c10_386_2, c10_386_3, c10_386_4, c10_386_5, c10_386_6, c10_386_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_388_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_388 :
    hubcapFit theRedpart rf10 p10_373l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_388_1, c10_388_2, c10_388_3, c10_388_4, c10_388_5, c10_388_6, c10_388_7, c10_388_8, c10_388_9, c10_388_10]

end FourColor

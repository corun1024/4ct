import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 8 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_372l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_372l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_390_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_390 :
    hubcapFit theRedpart rf10 p10_372l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_390_1, c10_390_2, c10_390_3, c10_390_4, c10_390_5, c10_390_6, c10_390_7, c10_390_8, c10_390_9, c10_390_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_371l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_371l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_371l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_392_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_371l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_392 :
    hubcapFit theRedpart rf10 p10_371l
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
  simp [hubcapFit, c10_392_1, c10_392_2, c10_392_3, c10_392_4, c10_392_5, c10_392_6, c10_392_7, c10_392_8, c10_392_9, c10_392_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_370l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_370l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_394_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_394 :
    hubcapFit theRedpart rf10 p10_370l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_394_1, c10_394_2, c10_394_3, c10_394_4, c10_394_5, c10_394_6, c10_394_7, c10_394_8, c10_394_9, c10_394_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_397l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_397l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_397l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_397l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_397l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_397l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_397l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_397l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_398_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_397l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_398 :
    hubcapFit theRedpart rf10 p10_397l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_398_1, c10_398_2, c10_398_3, c10_398_4, c10_398_5, c10_398_6, c10_398_7, c10_398_8, c10_398_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_401l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_401l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_401l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_401l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_402_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_401l) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_402 :
    hubcapFit theRedpart rf10 p10_401l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_402_1, c10_402_2, c10_402_3, c10_402_4, c10_402_5, c10_402_6, c10_402_7, c10_402_8, c10_402_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_401r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_401r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_401r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_401r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_404_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_401r) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_404 :
    hubcapFit theRedpart rf10 p10_401r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_404_1, c10_404_2, c10_404_3, c10_404_4, c10_404_5, c10_404_6, c10_404_7, c10_404_8, c10_404_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_400r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_400r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_400r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_400r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_400r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_400r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_400r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_400r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_407_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_400r) (hubSubn 10 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_407 :
    hubcapFit theRedpart rf10 p10_400r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_407_1, c10_407_2, c10_407_3, c10_407_4, c10_407_5, c10_407_6, c10_407_7, c10_407_8, c10_407_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_429r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_429r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_429r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_429r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_429r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_429r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_429r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_429r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_430_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_429r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_430 :
    hubcapFit theRedpart rf10 p10_429r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_430_1, c10_430_2, c10_430_3, c10_430_4, c10_430_5, c10_430_6, c10_430_7, c10_430_8, c10_430_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_436r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_436r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_436r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_436r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_436r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_436r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_436r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_436r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_437_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_436r) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_437 :
    hubcapFit theRedpart rf10 p10_436r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_437_1, c10_437_2, c10_437_3, c10_437_4, c10_437_5, c10_437_6, c10_437_7, c10_437_8, c10_437_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_436l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_436l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_436l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_436l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_436l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_436l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_436l) (hubSubn 10 9 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_438_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 7 p10_436l) (hubSubn 10 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_438 :
    hubcapFit theRedpart rf10 p10_436l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.two 1 9 6 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_438_1, c10_438_2, c10_438_3, c10_438_4, c10_438_5, c10_438_6, c10_438_7, c10_438_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_435l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_435l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_435l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_435l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_435l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_435l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_435l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_435l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_435l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_440_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_435l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_440 :
    hubcapFit theRedpart rf10 p10_435l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_440_1, c10_440_2, c10_440_3, c10_440_4, c10_440_5, c10_440_6, c10_440_7, c10_440_8, c10_440_9, c10_440_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_434l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_434l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_434l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_434l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_434l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_434l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_434l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_434l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_434l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_442_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_434l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_442 :
    hubcapFit theRedpart rf10 p10_434l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_442_1, c10_442_2, c10_442_3, c10_442_4, c10_442_5, c10_442_6, c10_442_7, c10_442_8, c10_442_9, c10_442_10]

end FourColor

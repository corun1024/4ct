import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 47 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2388l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2388l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2388l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2390_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2390 :
    hubcapFit theRedpart rf8 p8_2388l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2390_1, c8_2390_2, c8_2390_3, c8_2390_4, c8_2390_5, c8_2390_6, c8_2390_7, c8_2390_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2386l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2386l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2386l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2392_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2386l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2392 :
    hubcapFit theRedpart rf8 p8_2386l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2392_1, c8_2392_2, c8_2392_3, c8_2392_4, c8_2392_5, c8_2392_6, c8_2392_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2383l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2383l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2383l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2383l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2383l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2394_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2383l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2394 :
    hubcapFit theRedpart rf8 p8_2383l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2394_1, c8_2394_2, c8_2394_3, c8_2394_4, c8_2394_5, c8_2394_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2382l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2382l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2382l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2382l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2382l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2396_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2382l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2396 :
    hubcapFit theRedpart rf8 p8_2382l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2396_1, c8_2396_2, c8_2396_3, c8_2396_4, c8_2396_5, c8_2396_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2380l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2380l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2380l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2380l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2380l) (hubSubn 8 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2398_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2380l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2398 :
    hubcapFit theRedpart rf8 p8_2380l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2398_1, c8_2398_2, c8_2398_3, c8_2398_4, c8_2398_5, c8_2398_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2399_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2379l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2399_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2379l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2399_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2379l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2399_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2379l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2399_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2379l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2399 :
    hubcapFit theRedpart rf8 p8_2379l
    (Hubcap.one 2 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2399_1, c8_2399_2, c8_2399_3, c8_2399_4, c8_2399_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2378l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2378l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2378l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2378l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2401_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2378l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2401 :
    hubcapFit theRedpart rf8 p8_2378l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2401_1, c8_2401_2, c8_2401_3, c8_2401_4, c8_2401_5, c8_2401_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2377l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2377l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2377l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2377l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2377l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2402_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2377l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2402 :
    hubcapFit theRedpart rf8 p8_2377l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2402_1, c8_2402_2, c8_2402_3, c8_2402_4, c8_2402_5, c8_2402_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2414r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2414r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2414r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2414r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2414r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2414r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2415_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2414r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2415 :
    hubcapFit theRedpart rf8 p8_2414r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2415_1, c8_2415_2, c8_2415_3, c8_2415_4, c8_2415_5, c8_2415_6, c8_2415_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2414l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2414l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2416_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2416 :
    hubcapFit theRedpart rf8 p8_2414l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2416_1, c8_2416_2, c8_2416_3, c8_2416_4, c8_2416_5, c8_2416_6, c8_2416_7, c8_2416_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2413l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2413l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2413l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2418_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2413l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2418 :
    hubcapFit theRedpart rf8 p8_2413l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2418_1, c8_2418_2, c8_2418_3, c8_2418_4, c8_2418_5, c8_2418_6, c8_2418_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2411l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2411l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2420_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2411l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2420 :
    hubcapFit theRedpart rf8 p8_2411l
    (Hubcap.one 0 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2420_1, c8_2420_2, c8_2420_3, c8_2420_4, c8_2420_5, c8_2420_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2409l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2409l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2409l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2422_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2409l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2422 :
    hubcapFit theRedpart rf8 p8_2409l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2422_1, c8_2422_2, c8_2422_3, c8_2422_4, c8_2422_5, c8_2422_6, c8_2422_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2408l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2408l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2408l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2408l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2408l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2408l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2424_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2408l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2424 :
    hubcapFit theRedpart rf8 p8_2408l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2424_1, c8_2424_2, c8_2424_3, c8_2424_4, c8_2424_5, c8_2424_6, c8_2424_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2431r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2431r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2431r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2431r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2431r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2431r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2432_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2431r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2432 :
    hubcapFit theRedpart rf8 p8_2431r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2432_1, c8_2432_2, c8_2432_3, c8_2432_4, c8_2432_5, c8_2432_6, c8_2432_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2431l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2431l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2431l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2431l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2431l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2431l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2433_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2431l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2433 :
    hubcapFit theRedpart rf8 p8_2431l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2433_1, c8_2433_2, c8_2433_3, c8_2433_4, c8_2433_5, c8_2433_6, c8_2433_7]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 43 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2378_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2378_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2373l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2378_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2373l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2378_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2373l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2378_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2373l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2378 :
    hubcapFit theRedpart rf7 p7_2373l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2378_1, c7_2378_2, c7_2378_3, c7_2378_4, c7_2378_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2371l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2371l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2371l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2371l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2380_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2371l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2380 :
    hubcapFit theRedpart rf7 p7_2371l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2380_1, c7_2380_2, c7_2380_3, c7_2380_4, c7_2380_5, c7_2380_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2349l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2349l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2349l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2382_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2349l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2382 :
    hubcapFit theRedpart rf7 p7_2349l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2382_1, c7_2382_2, c7_2382_3, c7_2382_4, c7_2382_5, c7_2382_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2348l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2348l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2348l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2348l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2384_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2348l) (hubSubn 7 6 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2384 :
    hubcapFit theRedpart rf7 p7_2348l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2384_1, c7_2384_2, c7_2384_3, c7_2384_4, c7_2384_5, c7_2384_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2347l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2347l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2347l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2347l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2347l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2347l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2385_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2347l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2385 :
    hubcapFit theRedpart rf7 p7_2347l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2385_1, c7_2385_2, c7_2385_3, c7_2385_4, c7_2385_5, c7_2385_6, c7_2385_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2392_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2391r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2392_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2391r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2392_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2391r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2392_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2391r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2392_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2391r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2392 :
    hubcapFit theRedpart rf7 p7_2391r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2392_1, c7_2392_2, c7_2392_3, c7_2392_4, c7_2392_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2391l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2391l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2391l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2391l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2393_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2391l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2393 :
    hubcapFit theRedpart rf7 p7_2391l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2393_1, c7_2393_2, c7_2393_3, c7_2393_4, c7_2393_5, c7_2393_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2388l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2395_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2388l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2395 :
    hubcapFit theRedpart rf7 p7_2388l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2395_1, c7_2395_2, c7_2395_3, c7_2395_4, c7_2395_5, c7_2395_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2409r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2409r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2409r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2409r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2409r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2410_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2409r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2410 :
    hubcapFit theRedpart rf7 p7_2409r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2410_1, c7_2410_2, c7_2410_3, c7_2410_4, c7_2410_5, c7_2410_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2409l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2409l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2409l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2411_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2409l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2411 :
    hubcapFit theRedpart rf7 p7_2409l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2411_1, c7_2411_2, c7_2411_3, c7_2411_4, c7_2411_5, c7_2411_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2408l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2408l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2408l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2408l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2408l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2413_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2408l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2413 :
    hubcapFit theRedpart rf7 p7_2408l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2413_1, c7_2413_2, c7_2413_3, c7_2413_4, c7_2413_5, c7_2413_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2407l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2407l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2407l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2407l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2407l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2414_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2407l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2414 :
    hubcapFit theRedpart rf7 p7_2407l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2414_1, c7_2414_2, c7_2414_3, c7_2414_4, c7_2414_5, c7_2414_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2405l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2405l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2405l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2405l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2405l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2416_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2405l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2416 :
    hubcapFit theRedpart rf7 p7_2405l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2416_1, c7_2416_2, c7_2416_3, c7_2416_4, c7_2416_5, c7_2416_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2404l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2404l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2404l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2404l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2404l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2418_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2404l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2418 :
    hubcapFit theRedpart rf7 p7_2404l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2418_1, c7_2418_2, c7_2418_3, c7_2418_4, c7_2418_5, c7_2418_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2419_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2403l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2419_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2403l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2419_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2403l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2419_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2403l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2419_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2403l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2419 :
    hubcapFit theRedpart rf7 p7_2403l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2419_1, c7_2419_2, c7_2419_3, c7_2419_4, c7_2419_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2426r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2426r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2426r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2426r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2426r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2427_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2426r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2427 :
    hubcapFit theRedpart rf7 p7_2426r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2427_1, c7_2427_2, c7_2427_3, c7_2427_4, c7_2427_5, c7_2427_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2426l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2426l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2428_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2426l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2428 :
    hubcapFit theRedpart rf7 p7_2426l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2428_1, c7_2428_2, c7_2428_3, c7_2428_4, c7_2428_5, c7_2428_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2430_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2430_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2425l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2430_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2425l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2430_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2425l) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2430_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2425l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2430 :
    hubcapFit theRedpart rf7 p7_2425l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2430_1, c7_2430_2, c7_2430_3, c7_2430_4, c7_2430_5]

end FourColor

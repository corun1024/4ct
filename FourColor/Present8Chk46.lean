import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 46 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2226l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2226l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2226l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2226l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2226l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2330_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2226l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2330 :
    hubcapFit theRedpart rf8 p8_2226l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2330_1, c8_2330_2, c8_2330_3, c8_2330_4, c8_2330_5, c8_2330_6, c8_2330_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2049l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2049l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2049l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2332_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2049l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2332 :
    hubcapFit theRedpart rf8 p8_2049l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2332_1, c8_2332_2, c8_2332_3, c8_2332_4, c8_2332_5, c8_2332_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2048l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2048l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2334_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2048l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2334 :
    hubcapFit theRedpart rf8 p8_2048l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2334_1, c8_2334_2, c8_2334_3, c8_2334_4, c8_2334_5, c8_2334_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2047l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2047l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2335_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2047l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2335 :
    hubcapFit theRedpart rf8 p8_2047l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2335_1, c8_2335_2, c8_2335_3, c8_2335_4, c8_2335_5, c8_2335_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2352r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2352r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2352r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2352r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2352r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2352r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2353_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2352r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2353 :
    hubcapFit theRedpart rf8 p8_2352r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2353_1, c8_2353_2, c8_2353_3, c8_2353_4, c8_2353_5, c8_2353_6, c8_2353_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2352l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2354_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2354 :
    hubcapFit theRedpart rf8 p8_2352l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2354_1, c8_2354_2, c8_2354_3, c8_2354_4, c8_2354_5, c8_2354_6, c8_2354_7, c8_2354_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2351l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2356_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2351l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2356 :
    hubcapFit theRedpart rf8 p8_2351l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2356_1, c8_2356_2, c8_2356_3, c8_2356_4, c8_2356_5, c8_2356_6, c8_2356_7, c8_2356_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2358_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2350l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2358 :
    hubcapFit theRedpart rf8 p8_2350l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2358_1, c8_2358_2, c8_2358_3, c8_2358_4, c8_2358_5, c8_2358_6, c8_2358_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2349l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2349l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2360_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2349l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2360 :
    hubcapFit theRedpart rf8 p8_2349l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2360_1, c8_2360_2, c8_2360_3, c8_2360_4, c8_2360_5, c8_2360_6, c8_2360_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2368r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2368r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2368r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2368r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2368r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2368r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2369_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2368r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2369 :
    hubcapFit theRedpart rf8 p8_2368r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2369_1, c8_2369_2, c8_2369_3, c8_2369_4, c8_2369_5, c8_2369_6, c8_2369_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2368l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2368l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2368l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2368l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2368l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2370_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2368l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2370 :
    hubcapFit theRedpart rf8 p8_2368l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2370_1, c8_2370_2, c8_2370_3, c8_2370_4, c8_2370_5, c8_2370_6, c8_2370_7, c8_2370_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2365l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2365l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2365l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2365l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2365l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2365l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2372_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2365l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2372 :
    hubcapFit theRedpart rf8 p8_2365l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2372_1, c8_2372_2, c8_2372_3, c8_2372_4, c8_2372_5, c8_2372_6, c8_2372_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2364l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2364l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2364l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2364l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2364l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2374_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2364l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2374 :
    hubcapFit theRedpart rf8 p8_2364l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2374_1, c8_2374_2, c8_2374_3, c8_2374_4, c8_2374_5, c8_2374_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2375_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2363l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2375_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2375_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2363l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2375_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2363l) (hubSubn 8 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2375_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2363l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2375 :
    hubcapFit theRedpart rf8 p8_2363l
    (Hubcap.one 3 5 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2375_1, c8_2375_2, c8_2375_3, c8_2375_4, c8_2375_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2388r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2388r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2388r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2388r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2388r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2388r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2389_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2388r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2389 :
    hubcapFit theRedpart rf8 p8_2388r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2389_1, c8_2389_2, c8_2389_3, c8_2389_4, c8_2389_5, c8_2389_6, c8_2389_7]

end FourColor

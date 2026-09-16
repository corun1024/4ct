import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 50 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2362l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2362l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2370_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2362l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2370 :
    hubcapFit theRedpart rf9 p9_2362l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2370_1, c9_2370_2, c9_2370_3, c9_2370_4, c9_2370_5, c9_2370_6, c9_2370_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2361l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2361l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2361l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2361l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2361l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2361l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2372_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2361l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2372 :
    hubcapFit theRedpart rf9 p9_2361l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2372_1, c9_2372_2, c9_2372_3, c9_2372_4, c9_2372_5, c9_2372_6, c9_2372_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2360l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2360l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2360l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2360l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2360l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2360l) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2374_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2360l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2374 :
    hubcapFit theRedpart rf9 p9_2360l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2374_1, c9_2374_2, c9_2374_3, c9_2374_4, c9_2374_5, c9_2374_6, c9_2374_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2383r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2383r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2383r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2383r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2383r) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2384_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2383r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2384 :
    hubcapFit theRedpart rf9 p9_2383r
    (Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2384_1, c9_2384_2, c9_2384_3, c9_2384_4, c9_2384_5, c9_2384_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2393r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2393r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2393r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2394_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2393r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2394 :
    hubcapFit theRedpart rf9 p9_2393r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2394_1, c9_2394_2, c9_2394_3, c9_2394_4, c9_2394_5, c9_2394_6, c9_2394_7, c9_2394_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2393l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2393l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2393l) (hubSubn 9 7 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2395_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2393l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2395 :
    hubcapFit theRedpart rf9 p9_2393l
    (Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2395_1, c9_2395_2, c9_2395_3, c9_2395_4, c9_2395_5, c9_2395_6, c9_2395_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2392l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2397_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2397 :
    hubcapFit theRedpart rf9 p9_2392l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2397_1, c9_2397_2, c9_2397_3, c9_2397_4, c9_2397_5, c9_2397_6, c9_2397_7, c9_2397_8, c9_2397_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2390l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2390l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2390l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2399_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2399 :
    hubcapFit theRedpart rf9 p9_2390l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2399_1, c9_2399_2, c9_2399_3, c9_2399_4, c9_2399_5, c9_2399_6, c9_2399_7, c9_2399_8, c9_2399_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2401_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2389l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2401 :
    hubcapFit theRedpart rf9 p9_2389l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2401_1, c9_2401_2, c9_2401_3, c9_2401_4, c9_2401_5, c9_2401_6, c9_2401_7, c9_2401_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2403_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2388l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2403 :
    hubcapFit theRedpart rf9 p9_2388l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2403_1, c9_2403_2, c9_2403_3, c9_2403_4, c9_2403_5, c9_2403_6, c9_2403_7, c9_2403_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2386l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2386l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2386l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2386l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2405_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2386l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2405 :
    hubcapFit theRedpart rf9 p9_2386l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2405_1, c9_2405_2, c9_2405_3, c9_2405_4, c9_2405_5, c9_2405_6, c9_2405_7, c9_2405_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2380l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2380l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2380l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2380l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2380l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2407_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2380l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2407 :
    hubcapFit theRedpart rf9 p9_2380l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2407_1, c9_2407_2, c9_2407_3, c9_2407_4, c9_2407_5, c9_2407_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2379l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2379l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2379l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2379l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2379l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2409_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2379l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2409 :
    hubcapFit theRedpart rf9 p9_2379l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2409_1, c9_2409_2, c9_2409_3, c9_2409_4, c9_2409_5, c9_2409_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2415r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2415r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2415r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2415r) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2415r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2416_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2415r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2416 :
    hubcapFit theRedpart rf9 p9_2415r
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2416_1, c9_2416_2, c9_2416_3, c9_2416_4, c9_2416_5, c9_2416_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2415l) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2415l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2417_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2415l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2417 :
    hubcapFit theRedpart rf9 p9_2415l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2417_1, c9_2417_2, c9_2417_3, c9_2417_4, c9_2417_5, c9_2417_6]

end FourColor

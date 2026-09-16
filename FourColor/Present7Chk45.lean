import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 45 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2479_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2479_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2473l) (hubSubn 7 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2479_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2473l) (hubSubn 7 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2479_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2473l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2479 :
    hubcapFit theRedpart rf7 p7_2473l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2479_1, c7_2479_2, c7_2479_3, c7_2479_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2490r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2490r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2490r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2490r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2490r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2490r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2491_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2490r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2491 :
    hubcapFit theRedpart rf7 p7_2490r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2491_1, c7_2491_2, c7_2491_3, c7_2491_4, c7_2491_5, c7_2491_6, c7_2491_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2490l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2490l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2490l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2490l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2492_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2490l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2492 :
    hubcapFit theRedpart rf7 p7_2490l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2492_1, c7_2492_2, c7_2492_3, c7_2492_4, c7_2492_5, c7_2492_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2489l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2489l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2494_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2489l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2494 :
    hubcapFit theRedpart rf7 p7_2489l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2494_1, c7_2494_2, c7_2494_3, c7_2494_4, c7_2494_5, c7_2494_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2488l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2488l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2495_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2488l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2495 :
    hubcapFit theRedpart rf7 p7_2488l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2495_1, c7_2495_2, c7_2495_3, c7_2495_4, c7_2495_5, c7_2495_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2487l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2487l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2497_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2487l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2497 :
    hubcapFit theRedpart rf7 p7_2487l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2497_1, c7_2497_2, c7_2497_3, c7_2497_4, c7_2497_5, c7_2497_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2486l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2486l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2486l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2486l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2486l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2498_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2486l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2498 :
    hubcapFit theRedpart rf7 p7_2486l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2498_1, c7_2498_2, c7_2498_3, c7_2498_4, c7_2498_5, c7_2498_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2500_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2485l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2500_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2485l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2500_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2485l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2500_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2485l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2500_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2485l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2500 :
    hubcapFit theRedpart rf7 p7_2485l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2500_1, c7_2500_2, c7_2500_3, c7_2500_4, c7_2500_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2501r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2501r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2501r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2501r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2501r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2502_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2501r) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2502 :
    hubcapFit theRedpart rf7 p7_2501r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2502_1, c7_2502_2, c7_2502_3, c7_2502_4, c7_2502_5, c7_2502_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2501l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2501l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2501l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2503_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2501l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2503 :
    hubcapFit theRedpart rf7 p7_2501l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2503_1, c7_2503_2, c7_2503_3, c7_2503_4, c7_2503_5, c7_2503_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2510_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2509r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2510_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2509r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2510_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2509r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2510_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2509r) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2510_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2509r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2510 :
    hubcapFit theRedpart rf7 p7_2509r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2510_1, c7_2510_2, c7_2510_3, c7_2510_4, c7_2510_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2508l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2508l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2508l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2508l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2511_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2508l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2511 :
    hubcapFit theRedpart rf7 p7_2508l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2511_1, c7_2511_2, c7_2511_3, c7_2511_4, c7_2511_5, c7_2511_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2513_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2506l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2513_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2506l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2513_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2506l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2513_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2506l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2513_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2506l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2513 :
    hubcapFit theRedpart rf7 p7_2506l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2513_1, c7_2513_2, c7_2513_3, c7_2513_4, c7_2513_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2518_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2517r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2518_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2517r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2518_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2517r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2518_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2517r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2518_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2517r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2518 :
    hubcapFit theRedpart rf7 p7_2517r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2518_1, c7_2518_2, c7_2518_3, c7_2518_4, c7_2518_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2517l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2517l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2517l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2519_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2517l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2519 :
    hubcapFit theRedpart rf7 p7_2517l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2519_1, c7_2519_2, c7_2519_3, c7_2519_4, c7_2519_5, c7_2519_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2521_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2516l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2521_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2516l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2521_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2516l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2521_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2516l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2521_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2516l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2521 :
    hubcapFit theRedpart rf7 p7_2516l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2521_1, c7_2521_2, c7_2521_3, c7_2521_4, c7_2521_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2515l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2515l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2515l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2515l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2515l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2515l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2522_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2515l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2522 :
    hubcapFit theRedpart rf7 p7_2515l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2522_1, c7_2522_2, c7_2522_3, c7_2522_4, c7_2522_5, c7_2522_6, c7_2522_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2533_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2532r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2533_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2532r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2533_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2532r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2533_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2532r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2533_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2532r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2533 :
    hubcapFit theRedpart rf7 p7_2532r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2533_1, c7_2533_2, c7_2533_3, c7_2533_4, c7_2533_5]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 51 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2570r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2570r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2570r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2570r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2570r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2573_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2570r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2573 :
    hubcapFit theRedpart rf8 p8_2570r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2573_1, c8_2573_2, c8_2573_3, c8_2573_4, c8_2573_5, c8_2573_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2576l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2576l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2576l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2576l) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2576l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2577_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2576l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2577 :
    hubcapFit theRedpart rf8 p8_2576l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2577_1, c8_2577_2, c8_2577_3, c8_2577_4, c8_2577_5, c8_2577_6, c8_2577_7, c8_2577_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2576r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2576r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2576r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2576r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2576r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2576r) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2576r) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2579_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2576r) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2579 :
    hubcapFit theRedpart rf8 p8_2576r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2579_1, c8_2579_2, c8_2579_3, c8_2579_4, c8_2579_5, c8_2579_6, c8_2579_7, c8_2579_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2585r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2585r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2585r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2585r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2585r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2585r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2586_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2585r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2586 :
    hubcapFit theRedpart rf8 p8_2585r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2586_1, c8_2586_2, c8_2586_3, c8_2586_4, c8_2586_5, c8_2586_6, c8_2586_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2585l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2585l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2585l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2585l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2585l) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2587_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2585l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2587 :
    hubcapFit theRedpart rf8 p8_2585l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2587_1, c8_2587_2, c8_2587_3, c8_2587_4, c8_2587_5, c8_2587_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2584l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2584l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2584l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2584l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2584l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2589_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2584l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2589 :
    hubcapFit theRedpart rf8 p8_2584l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2589_1, c8_2589_2, c8_2589_3, c8_2589_4, c8_2589_5, c8_2589_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2583l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2583l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2583l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2583l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2583l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2590_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2583l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2590 :
    hubcapFit theRedpart rf8 p8_2583l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2590_1, c8_2590_2, c8_2590_3, c8_2590_4, c8_2590_5, c8_2590_6, c8_2590_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2594_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2593l) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2594 :
    hubcapFit theRedpart rf8 p8_2593l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2594_1, c8_2594_2, c8_2594_3, c8_2594_4, c8_2594_5, c8_2594_6, c8_2594_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2593r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2593r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2593r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2593r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2593r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2593r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2596_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2593r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2596 :
    hubcapFit theRedpart rf8 p8_2593r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2596_1, c8_2596_2, c8_2596_3, c8_2596_4, c8_2596_5, c8_2596_6, c8_2596_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2599l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2599l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2599l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2599l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2599l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2600_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2599l) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2600 :
    hubcapFit theRedpart rf8 p8_2599l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2600_1, c8_2600_2, c8_2600_3, c8_2600_4, c8_2600_5, c8_2600_6, c8_2600_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2599r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2599r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2599r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2599r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2599r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2599r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2602_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2599r) (hubSubn 8 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2602 :
    hubcapFit theRedpart rf8 p8_2599r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2602_1, c8_2602_2, c8_2602_3, c8_2602_4, c8_2602_5, c8_2602_6, c8_2602_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2487l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2487l) (hubSubn 8 7 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2487l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2487l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2605_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2487l) (hubSubn 8 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2605 :
    hubcapFit theRedpart rf8 p8_2487l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 7 6 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2605_1, c8_2605_2, c8_2605_3, c8_2605_4, c8_2605_5, c8_2605_6, c8_2605_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2624r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2624r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2624r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2624r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2624r) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2625_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2624r) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2625 :
    hubcapFit theRedpart rf8 p8_2624r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2625_1, c8_2625_2, c8_2625_3, c8_2625_4, c8_2625_5, c8_2625_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2624l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2624l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2624l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2626_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2624l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2626 :
    hubcapFit theRedpart rf8 p8_2624l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2626_1, c8_2626_2, c8_2626_3, c8_2626_4, c8_2626_5, c8_2626_6, c8_2626_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2623l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2623l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2623l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2623l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2623l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2628_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2623l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2628 :
    hubcapFit theRedpart rf8 p8_2623l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2628_1, c8_2628_2, c8_2628_3, c8_2628_4, c8_2628_5, c8_2628_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2620l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2620l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2620l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2630_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2620l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2630 :
    hubcapFit theRedpart rf8 p8_2620l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2630_1, c8_2630_2, c8_2630_3, c8_2630_4, c8_2630_5, c8_2630_6, c8_2630_7]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 54 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2575l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2575l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2575l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2575l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2575l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2575l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2577_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2575l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2577 :
    hubcapFit theRedpart rf9 p9_2575l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2577_1, c9_2577_2, c9_2577_3, c9_2577_4, c9_2577_5, c9_2577_6, c9_2577_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2573l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2573l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2573l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2573l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2573l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2573l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2579_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2573l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2579 :
    hubcapFit theRedpart rf9 p9_2573l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2579_1, c9_2579_2, c9_2579_3, c9_2579_4, c9_2579_5, c9_2579_6, c9_2579_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2571l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2571l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2571l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2571l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2571l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2581_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2571l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2581 :
    hubcapFit theRedpart rf9 p9_2571l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2581_1, c9_2581_2, c9_2581_3, c9_2581_4, c9_2581_5, c9_2581_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2568l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2568l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2583_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2568l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2583 :
    hubcapFit theRedpart rf9 p9_2568l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2583_1, c9_2583_2, c9_2583_3, c9_2583_4, c9_2583_5, c9_2583_6, c9_2583_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2567l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2567l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2567l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2567l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2567l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2567l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2585_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2567l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2585 :
    hubcapFit theRedpart rf9 p9_2567l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2585_1, c9_2585_2, c9_2585_3, c9_2585_4, c9_2585_5, c9_2585_6, c9_2585_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2565l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2565l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2587_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2565l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2587 :
    hubcapFit theRedpart rf9 p9_2565l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2587_1, c9_2587_2, c9_2587_3, c9_2587_4, c9_2587_5, c9_2587_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2563l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2563l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2563l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2563l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2563l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2589_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2563l) (hubSubn 9 7 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2589 :
    hubcapFit theRedpart rf9 p9_2563l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2589_1, c9_2589_2, c9_2589_3, c9_2589_4, c9_2589_5, c9_2589_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2561l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2561l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2561l) (hubSubn 9 7 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2561l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2591_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2561l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2591 :
    hubcapFit theRedpart rf9 p9_2561l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 7 8 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2591_1, c9_2591_2, c9_2591_3, c9_2591_4, c9_2591_5, c9_2591_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2560l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2560l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2593_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2560l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2593 :
    hubcapFit theRedpart rf9 p9_2560l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2593_1, c9_2593_2, c9_2593_3, c9_2593_4, c9_2593_5, c9_2593_6, c9_2593_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2559l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2559l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2595_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2559l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2595 :
    hubcapFit theRedpart rf9 p9_2559l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2595_1, c9_2595_2, c9_2595_3, c9_2595_4, c9_2595_5, c9_2595_6, c9_2595_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2556l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2556l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2556l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2556l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2556l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2556l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2597_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2556l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2597 :
    hubcapFit theRedpart rf9 p9_2556l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2597_1, c9_2597_2, c9_2597_3, c9_2597_4, c9_2597_5, c9_2597_6, c9_2597_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2555l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2555l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2599_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2555l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2599 :
    hubcapFit theRedpart rf9 p9_2555l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2599_1, c9_2599_2, c9_2599_3, c9_2599_4, c9_2599_5, c9_2599_6, c9_2599_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2554l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2554l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2554l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2601_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2554l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2601 :
    hubcapFit theRedpart rf9 p9_2554l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2601_1, c9_2601_2, c9_2601_3, c9_2601_4, c9_2601_5, c9_2601_6, c9_2601_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2553l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2553l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2553l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2603_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2553l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2603 :
    hubcapFit theRedpart rf9 p9_2553l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2603_1, c9_2603_2, c9_2603_3, c9_2603_4, c9_2603_5, c9_2603_6, c9_2603_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2552l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2552l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2552l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2552l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2552l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2605_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2552l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2605 :
    hubcapFit theRedpart rf9 p9_2552l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2605_1, c9_2605_2, c9_2605_3, c9_2605_4, c9_2605_5, c9_2605_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2551l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2551l) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2551l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2606_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2551l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2606 :
    hubcapFit theRedpart rf9 p9_2551l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2606_1, c9_2606_2, c9_2606_3, c9_2606_4, c9_2606_5, c9_2606_6]

end FourColor

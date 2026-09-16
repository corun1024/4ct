import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 56 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2623l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2623l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2623l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2623l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2661_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2623l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2661 :
    hubcapFit theRedpart rf9 p9_2623l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2661_1, c9_2661_2, c9_2661_3, c9_2661_4, c9_2661_5, c9_2661_6, c9_2661_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2622l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2622l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2622l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2622l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2622l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2622l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2663_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2622l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2663 :
    hubcapFit theRedpart rf9 p9_2622l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2663_1, c9_2663_2, c9_2663_3, c9_2663_4, c9_2663_5, c9_2663_6, c9_2663_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2621l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2621l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2621l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2665_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2621l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2665 :
    hubcapFit theRedpart rf9 p9_2621l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2665_1, c9_2665_2, c9_2665_3, c9_2665_4, c9_2665_5, c9_2665_6, c9_2665_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2620l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2620l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2620l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2667_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2620l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2667 :
    hubcapFit theRedpart rf9 p9_2620l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2667_1, c9_2667_2, c9_2667_3, c9_2667_4, c9_2667_5, c9_2667_6, c9_2667_7, c9_2667_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2619l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2619l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2619l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2619l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2669_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2619l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2669 :
    hubcapFit theRedpart rf9 p9_2619l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2669_1, c9_2669_2, c9_2669_3, c9_2669_4, c9_2669_5, c9_2669_6, c9_2669_7, c9_2669_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2618l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2618l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2671_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2618l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2671 :
    hubcapFit theRedpart rf9 p9_2618l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2671_1, c9_2671_2, c9_2671_3, c9_2671_4, c9_2671_5, c9_2671_6, c9_2671_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2617l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2617l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2617l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2617l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2673_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2617l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2673 :
    hubcapFit theRedpart rf9 p9_2617l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2673_1, c9_2673_2, c9_2673_3, c9_2673_4, c9_2673_5, c9_2673_6, c9_2673_7, c9_2673_8, c9_2673_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2616l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2616l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2616l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2616l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2616l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2675_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2616l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2675 :
    hubcapFit theRedpart rf9 p9_2616l
    (Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2675_1, c9_2675_2, c9_2675_3, c9_2675_4, c9_2675_5, c9_2675_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2691r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2691r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2691r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2691r) (hubSubn 9 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2691r) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2692_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2691r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2692 :
    hubcapFit theRedpart rf9 p9_2691r
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2692_1, c9_2692_2, c9_2692_3, c9_2692_4, c9_2692_5, c9_2692_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2696r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2696r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2696r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2696r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2696r) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2697_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2696r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2697 :
    hubcapFit theRedpart rf9 p9_2696r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2697_1, c9_2697_2, c9_2697_3, c9_2697_4, c9_2697_5, c9_2697_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2696l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2696l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2696l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2696l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2696l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2698_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2696l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2698 :
    hubcapFit theRedpart rf9 p9_2696l
    (Hubcap.one 2 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2698_1, c9_2698_2, c9_2698_3, c9_2698_4, c9_2698_5, c9_2698_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2694l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2694l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2694l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2694l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2694l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2700_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2694l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2700 :
    hubcapFit theRedpart rf9 p9_2694l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2700_1, c9_2700_2, c9_2700_3, c9_2700_4, c9_2700_5, c9_2700_6, c9_2700_7, c9_2700_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2685l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2685l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2685l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2685l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2685l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2685l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2685l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2703_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2685l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2703 :
    hubcapFit theRedpart rf9 p9_2685l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2703_1, c9_2703_2, c9_2703_3, c9_2703_4, c9_2703_5, c9_2703_6, c9_2703_7, c9_2703_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2684l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2684l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2684l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2684l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2705_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2684l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2705 :
    hubcapFit theRedpart rf9 p9_2684l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2705_1, c9_2705_2, c9_2705_3, c9_2705_4, c9_2705_5, c9_2705_6, c9_2705_7, c9_2705_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2683l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2683l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2707_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2683l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2707 :
    hubcapFit theRedpart rf9 p9_2683l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2707_1, c9_2707_2, c9_2707_3, c9_2707_4, c9_2707_5, c9_2707_6, c9_2707_7]

end FourColor

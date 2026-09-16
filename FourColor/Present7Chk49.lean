import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 49 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2686_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2686_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2676l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2686_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2676l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2686_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2676l) (hubSubn 7 5 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2686_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2676l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2686 :
    hubcapFit theRedpart rf7 p7_2676l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 5 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2686_1, c7_2686_2, c7_2686_3, c7_2686_4, c7_2686_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2690_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2689r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2690_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2689r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2690_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2689r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2690_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2689r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2690_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2689r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2690 :
    hubcapFit theRedpart rf7 p7_2689r
    (Hubcap.one 0 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2690_1, c7_2690_2, c7_2690_3, c7_2690_4, c7_2690_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2691_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2689l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2691_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2689l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2691_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2689l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2691_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2689l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2691_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2689l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2691 :
    hubcapFit theRedpart rf7 p7_2689l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2691_1, c7_2691_2, c7_2691_3, c7_2691_4, c7_2691_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2696r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2696r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2696r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2697_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2697 :
    hubcapFit theRedpart rf7 p7_2696r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2697_1, c7_2697_2, c7_2697_3, c7_2697_4, c7_2697_5, c7_2697_6, c7_2697_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2698_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2698_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2696l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2698_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2696l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2698_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2696l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2698_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2696l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2698 :
    hubcapFit theRedpart rf7 p7_2696l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2698_1, c7_2698_2, c7_2698_3, c7_2698_4, c7_2698_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2701_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2700r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2701_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2700r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2701_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2700r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2701_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2700r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2701_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2700r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2701 :
    hubcapFit theRedpart rf7 p7_2700r
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2701_1, c7_2701_2, c7_2701_3, c7_2701_4, c7_2701_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2700l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2700l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2700l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2702_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2700l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2702 :
    hubcapFit theRedpart rf7 p7_2700l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2702_1, c7_2702_2, c7_2702_3, c7_2702_4, c7_2702_5, c7_2702_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2707r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2707r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2707r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2707r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2707r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2708_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2707r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2708 :
    hubcapFit theRedpart rf7 p7_2707r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2708_1, c7_2708_2, c7_2708_3, c7_2708_4, c7_2708_5, c7_2708_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2707l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2707l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2707l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2707l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2709_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2707l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2709 :
    hubcapFit theRedpart rf7 p7_2707l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2709_1, c7_2709_2, c7_2709_3, c7_2709_4, c7_2709_5, c7_2709_6, c7_2709_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2706l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2706l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2706l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2706l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2711_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2706l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2711 :
    hubcapFit theRedpart rf7 p7_2706l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2711_1, c7_2711_2, c7_2711_3, c7_2711_4, c7_2711_5, c7_2711_6, c7_2711_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2713_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2713_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2705l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2713_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2705l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2713_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2705l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2713_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2705l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2713 :
    hubcapFit theRedpart rf7 p7_2705l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2713_1, c7_2713_2, c7_2713_3, c7_2713_4, c7_2713_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2704l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2704l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2714_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2704l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2714 :
    hubcapFit theRedpart rf7 p7_2704l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2714_1, c7_2714_2, c7_2714_3, c7_2714_4, c7_2714_5, c7_2714_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2723r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2723r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2723r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2723r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2723r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2723r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2724_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2723r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2724 :
    hubcapFit theRedpart rf7 p7_2723r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2724_1, c7_2724_2, c7_2724_3, c7_2724_4, c7_2724_5, c7_2724_6, c7_2724_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2723l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2723l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2723l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2723l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2723l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2725_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2723l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2725 :
    hubcapFit theRedpart rf7 p7_2723l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2725_1, c7_2725_2, c7_2725_3, c7_2725_4, c7_2725_5, c7_2725_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2721l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2721l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2721l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2727_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2721l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2727 :
    hubcapFit theRedpart rf7 p7_2721l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2727_1, c7_2727_2, c7_2727_3, c7_2727_4, c7_2727_5, c7_2727_6, c7_2727_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2720l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2720l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2720l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2720l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2720l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2729_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2720l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2729 :
    hubcapFit theRedpart rf7 p7_2720l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2729_1, c7_2729_2, c7_2729_3, c7_2729_4, c7_2729_5, c7_2729_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2719l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2719l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2719l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2719l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2719l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2730_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2719l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2730 :
    hubcapFit theRedpart rf7 p7_2719l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2730_1, c7_2730_2, c7_2730_3, c7_2730_4, c7_2730_5, c7_2730_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2734r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2734r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2734r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2734r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2734r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2735_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2734r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2735 :
    hubcapFit theRedpart rf7 p7_2734r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2735_1, c7_2735_2, c7_2735_3, c7_2735_4, c7_2735_5, c7_2735_6]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 51 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2779l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2779l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2791_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2779l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2791 :
    hubcapFit theRedpart rf7 p7_2779l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2791_1, c7_2791_2, c7_2791_3, c7_2791_4, c7_2791_5, c7_2791_6, c7_2791_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2778l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2778l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2778l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2778l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2793_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2778l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2793 :
    hubcapFit theRedpart rf7 p7_2778l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2793_1, c7_2793_2, c7_2793_3, c7_2793_4, c7_2793_5, c7_2793_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2776l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2776l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2776l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2776l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2795_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2776l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2795 :
    hubcapFit theRedpart rf7 p7_2776l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2795_1, c7_2795_2, c7_2795_3, c7_2795_4, c7_2795_5, c7_2795_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2797_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2774l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2797_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2774l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2797_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2774l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2797_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2774l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2797_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2774l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2797 :
    hubcapFit theRedpart rf7 p7_2774l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2797_1, c7_2797_2, c7_2797_3, c7_2797_4, c7_2797_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2798_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2773l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2798_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2773l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2798_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2773l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2798_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2773l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2798 :
    hubcapFit theRedpart rf7 p7_2773l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2798_1, c7_2798_2, c7_2798_3, c7_2798_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2772l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2772l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2772l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2772l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2772l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2800_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2772l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2800 :
    hubcapFit theRedpart rf7 p7_2772l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2800_1, c7_2800_2, c7_2800_3, c7_2800_4, c7_2800_5, c7_2800_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2805_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2804r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2805_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2804r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2805_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2804r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2805_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2804r) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2805_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2804r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2805 :
    hubcapFit theRedpart rf7 p7_2804r
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2805_1, c7_2805_2, c7_2805_3, c7_2805_4, c7_2805_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2804l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2804l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2804l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2806_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2804l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2806 :
    hubcapFit theRedpart rf7 p7_2804l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2806_1, c7_2806_2, c7_2806_3, c7_2806_4, c7_2806_5, c7_2806_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2808_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2803l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2808_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2803l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2808_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2803l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2808_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2803l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2808_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2803l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2808 :
    hubcapFit theRedpart rf7 p7_2803l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2808_1, c7_2808_2, c7_2808_3, c7_2808_4, c7_2808_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2809_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2802l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2809_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2802l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2809_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2802l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2809_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2802l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2809 :
    hubcapFit theRedpart rf7 p7_2802l
    (Hubcap.one 4 0 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2809_1, c7_2809_2, c7_2809_3, c7_2809_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2801l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2801l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2801l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2811_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2801l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2811 :
    hubcapFit theRedpart rf7 p7_2801l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2811_1, c7_2811_2, c7_2811_3, c7_2811_4, c7_2811_5, c7_2811_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2820r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2820r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2820r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2820r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2820r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2821_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2820r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2821 :
    hubcapFit theRedpart rf7 p7_2820r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2821_1, c7_2821_2, c7_2821_3, c7_2821_4, c7_2821_5, c7_2821_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2820l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2820l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2820l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2820l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2822_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2820l) (hubSubn 7 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2822 :
    hubcapFit theRedpart rf7 p7_2820l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2822_1, c7_2822_2, c7_2822_3, c7_2822_4, c7_2822_5, c7_2822_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2824_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2819l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2824_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2819l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2824_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2819l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2824_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2819l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2824_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2819l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2824 :
    hubcapFit theRedpart rf7 p7_2819l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2824_1, c7_2824_2, c7_2824_3, c7_2824_4, c7_2824_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2817l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2817l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2817l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2817l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2817l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2826_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2817l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2826 :
    hubcapFit theRedpart rf7 p7_2817l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2826_1, c7_2826_2, c7_2826_3, c7_2826_4, c7_2826_5, c7_2826_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2816l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2816l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2816l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2827_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2816l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2827 :
    hubcapFit theRedpart rf7 p7_2816l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2827_1, c7_2827_2, c7_2827_3, c7_2827_4, c7_2827_5, c7_2827_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2829r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2829r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2829r) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2829r) (hubSubn 7 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2830_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2829r) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2830 :
    hubcapFit theRedpart rf7 p7_2829r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2830_1, c7_2830_2, c7_2830_3, c7_2830_4, c7_2830_5, c7_2830_6, c7_2830_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2829l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2829l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2829l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2831_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2829l) (hubSubn 7 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2831 :
    hubcapFit theRedpart rf7 p7_2829l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2831_1, c7_2831_2, c7_2831_3, c7_2831_4, c7_2831_5, c7_2831_6]

end FourColor

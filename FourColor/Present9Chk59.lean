import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 59 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2808l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2808l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2808l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2808l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2808l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2808l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2817_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2808l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2817 :
    hubcapFit theRedpart rf9 p9_2808l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2817_1, c9_2817_2, c9_2817_3, c9_2817_4, c9_2817_5, c9_2817_6, c9_2817_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2819_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2805l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2819_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2805l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2819_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2805l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2819_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2805l) (hubSubn 9 7 5) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2819_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2805l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2819 :
    hubcapFit theRedpart rf9 p9_2805l
    (Hubcap.one 4 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 7 9 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2819_1, c9_2819_2, c9_2819_3, c9_2819_4, c9_2819_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2803l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2803l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2803l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2803l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2803l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2803l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2803l) (hubSubn 9 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2821_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2803l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2821 :
    hubcapFit theRedpart rf9 p9_2803l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2821_1, c9_2821_2, c9_2821_3, c9_2821_4, c9_2821_5, c9_2821_6, c9_2821_7, c9_2821_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2801l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2801l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2823_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2801l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2823 :
    hubcapFit theRedpart rf9 p9_2801l
    (Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2823_1, c9_2823_2, c9_2823_3, c9_2823_4, c9_2823_5, c9_2823_6, c9_2823_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2799l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2799l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2799l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2799l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2825_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2799l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2825 :
    hubcapFit theRedpart rf9 p9_2799l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2825_1, c9_2825_2, c9_2825_3, c9_2825_4, c9_2825_5, c9_2825_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2798l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2798l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2798l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2798l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2798l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2798l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2827_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2798l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2827 :
    hubcapFit theRedpart rf9 p9_2798l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2827_1, c9_2827_2, c9_2827_3, c9_2827_4, c9_2827_5, c9_2827_6, c9_2827_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2797l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2797l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2797l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2797l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2797l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2797l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2797l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2829_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2797l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2829 :
    hubcapFit theRedpart rf9 p9_2797l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2829_1, c9_2829_2, c9_2829_3, c9_2829_4, c9_2829_5, c9_2829_6, c9_2829_7, c9_2829_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2796l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2796l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2796l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2796l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2796l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2796l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2796l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2831_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2796l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2831 :
    hubcapFit theRedpart rf9 p9_2796l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2831_1, c9_2831_2, c9_2831_3, c9_2831_4, c9_2831_5, c9_2831_6, c9_2831_7, c9_2831_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2795l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2795l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2795l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2795l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2833_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2795l) (hubSubn 9 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2833 :
    hubcapFit theRedpart rf9 p9_2795l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2833_1, c9_2833_2, c9_2833_3, c9_2833_4, c9_2833_5, c9_2833_6, c9_2833_7, c9_2833_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2794l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2794l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2794l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2794l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2794l) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2835_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2794l) (hubSubn 9 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2835 :
    hubcapFit theRedpart rf9 p9_2794l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 1 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2835_1, c9_2835_2, c9_2835_3, c9_2835_4, c9_2835_5, c9_2835_6, c9_2835_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2847r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2847r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2847r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2847r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2847r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2848_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2847r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2848 :
    hubcapFit theRedpart rf9 p9_2847r
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2848_1, c9_2848_2, c9_2848_3, c9_2848_4, c9_2848_5, c9_2848_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2847l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2847l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2847l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2847l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2847l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2849_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2847l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2849 :
    hubcapFit theRedpart rf9 p9_2847l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2849_1, c9_2849_2, c9_2849_3, c9_2849_4, c9_2849_5, c9_2849_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2846l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2846l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2851_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2846l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2851 :
    hubcapFit theRedpart rf9 p9_2846l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2851_1, c9_2851_2, c9_2851_3, c9_2851_4, c9_2851_5, c9_2851_6, c9_2851_7, c9_2851_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2861r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2861r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2861r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2861r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2861r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2861r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2862_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2861r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2862 :
    hubcapFit theRedpart rf9 p9_2861r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2862_1, c9_2862_2, c9_2862_3, c9_2862_4, c9_2862_5, c9_2862_6, c9_2862_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2861l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2861l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2861l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2861l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2861l) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2863_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2861l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2863 :
    hubcapFit theRedpart rf9 p9_2861l
    (Hubcap.one 0 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2863_1, c9_2863_2, c9_2863_3, c9_2863_4, c9_2863_5, c9_2863_6]

end FourColor

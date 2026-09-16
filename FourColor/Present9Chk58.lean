import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 58 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2763l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2763l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2763l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2771_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2763l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2771 :
    hubcapFit theRedpart rf9 p9_2763l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2771_1, c9_2771_2, c9_2771_3, c9_2771_4, c9_2771_5, c9_2771_6, c9_2771_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2762l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2762l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2762l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2762l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2773_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2762l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2773 :
    hubcapFit theRedpart rf9 p9_2762l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2773_1, c9_2773_2, c9_2773_3, c9_2773_4, c9_2773_5, c9_2773_6, c9_2773_7, c9_2773_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2761l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2761l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2761l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2761l) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2761l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2775_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2761l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2775 :
    hubcapFit theRedpart rf9 p9_2761l
    (Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2775_1, c9_2775_2, c9_2775_3, c9_2775_4, c9_2775_5, c9_2775_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2760l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2760l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2760l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2760l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2760l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2776_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2760l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2776 :
    hubcapFit theRedpart rf9 p9_2760l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2776_1, c9_2776_2, c9_2776_3, c9_2776_4, c9_2776_5, c9_2776_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2758l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2758l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2758l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2758l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2758l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2778_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2758l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2778 :
    hubcapFit theRedpart rf9 p9_2758l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2778_1, c9_2778_2, c9_2778_3, c9_2778_4, c9_2778_5, c9_2778_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2742l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2742l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2781_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2742l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2781 :
    hubcapFit theRedpart rf9 p9_2742l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2781_1, c9_2781_2, c9_2781_3, c9_2781_4, c9_2781_5, c9_2781_6, c9_2781_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2740l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2740l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2783_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2740l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2783 :
    hubcapFit theRedpart rf9 p9_2740l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2783_1, c9_2783_2, c9_2783_3, c9_2783_4, c9_2783_5, c9_2783_6, c9_2783_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2739l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2739l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2739l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2739l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2739l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2785_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2739l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2785 :
    hubcapFit theRedpart rf9 p9_2739l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2785_1, c9_2785_2, c9_2785_3, c9_2785_4, c9_2785_5, c9_2785_6, c9_2785_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2738l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2738l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2738l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2738l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2787_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2738l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2787 :
    hubcapFit theRedpart rf9 p9_2738l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2787_1, c9_2787_2, c9_2787_3, c9_2787_4, c9_2787_5, c9_2787_6, c9_2787_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2737l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2737l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2737l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2737l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2789_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2737l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2789 :
    hubcapFit theRedpart rf9 p9_2737l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2789_1, c9_2789_2, c9_2789_3, c9_2789_4, c9_2789_5, c9_2789_6, c9_2789_7, c9_2789_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2736l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2736l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2736l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2791_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2736l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2791 :
    hubcapFit theRedpart rf9 p9_2736l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2791_1, c9_2791_2, c9_2791_3, c9_2791_4, c9_2791_5, c9_2791_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2735l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2735l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2735l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2792_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2735l) (hubSubn 9 8 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2792 :
    hubcapFit theRedpart rf9 p9_2735l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2792_1, c9_2792_2, c9_2792_3, c9_2792_4, c9_2792_5, c9_2792_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2811r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2811r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2811r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2811r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2811r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2811r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2811r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2811r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2812_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2811r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2812 :
    hubcapFit theRedpart rf9 p9_2811r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2812_1, c9_2812_2, c9_2812_3, c9_2812_4, c9_2812_5, c9_2812_6, c9_2812_7, c9_2812_8, c9_2812_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2811l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2811l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2811l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2811l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2811l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2811l) (hubSubn 9 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2813_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2811l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2813 :
    hubcapFit theRedpart rf9 p9_2811l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2813_1, c9_2813_2, c9_2813_3, c9_2813_4, c9_2813_5, c9_2813_6, c9_2813_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2810l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2810l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2810l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2810l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2810l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2810l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2815_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2810l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2815 :
    hubcapFit theRedpart rf9 p9_2810l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2815_1, c9_2815_2, c9_2815_3, c9_2815_4, c9_2815_5, c9_2815_6, c9_2815_7]

end FourColor

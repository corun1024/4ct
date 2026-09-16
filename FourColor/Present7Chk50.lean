import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 50 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2734l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2734l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2734l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2736_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2736 :
    hubcapFit theRedpart rf7 p7_2734l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2736_1, c7_2736_2, c7_2736_3, c7_2736_4, c7_2736_5, c7_2736_6, c7_2736_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2733l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2733l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2733l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2733l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2733l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2738_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2738 :
    hubcapFit theRedpart rf7 p7_2733l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2738_1, c7_2738_2, c7_2738_3, c7_2738_4, c7_2738_5, c7_2738_6, c7_2738_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2740r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2740r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2740r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2740r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2740r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2741_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2740r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2741 :
    hubcapFit theRedpart rf7 p7_2740r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2741_1, c7_2741_2, c7_2741_3, c7_2741_4, c7_2741_5, c7_2741_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2740l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2740l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2742_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2740l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2742 :
    hubcapFit theRedpart rf7 p7_2740l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2742_1, c7_2742_2, c7_2742_3, c7_2742_4, c7_2742_5, c7_2742_6, c7_2742_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2753r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2753r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2753r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2753r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2753r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2754_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2753r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2754 :
    hubcapFit theRedpart rf7 p7_2753r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2754_1, c7_2754_2, c7_2754_3, c7_2754_4, c7_2754_5, c7_2754_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2753l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2753l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2753l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2753l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2753l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2755_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2753l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2755 :
    hubcapFit theRedpart rf7 p7_2753l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2755_1, c7_2755_2, c7_2755_3, c7_2755_4, c7_2755_5, c7_2755_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2751l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2751l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2751l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2751l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2751l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2757_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2751l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2757 :
    hubcapFit theRedpart rf7 p7_2751l
    (Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2757_1, c7_2757_2, c7_2757_3, c7_2757_4, c7_2757_5, c7_2757_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2750l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2750l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2750l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2750l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2750l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2759_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2750l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2759 :
    hubcapFit theRedpart rf7 p7_2750l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2759_1, c7_2759_2, c7_2759_3, c7_2759_4, c7_2759_5, c7_2759_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2762r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2762r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2762r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2762r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2762r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2763_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2762r) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2763 :
    hubcapFit theRedpart rf7 p7_2762r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 2 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2763_1, c7_2763_2, c7_2763_3, c7_2763_4, c7_2763_5, c7_2763_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2762l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2762l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2762l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2764_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2762l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2764 :
    hubcapFit theRedpart rf7 p7_2762l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 2 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2764_1, c7_2764_2, c7_2764_3, c7_2764_4, c7_2764_5, c7_2764_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2761l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2761l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2761l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2761l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2761l) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2766_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2761l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2766 :
    hubcapFit theRedpart rf7 p7_2761l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2766_1, c7_2766_2, c7_2766_3, c7_2766_4, c7_2766_5, c7_2766_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2767_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2760l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2767_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2760l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2767_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2760l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2767_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2760l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2767_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2760l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2767 :
    hubcapFit theRedpart rf7 p7_2760l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2767_1, c7_2767_2, c7_2767_3, c7_2767_4, c7_2767_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2770_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2748l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2770_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2748l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2770_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2748l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2770_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2748l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2770_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2748l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2770 :
    hubcapFit theRedpart rf7 p7_2748l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2770_1, c7_2770_2, c7_2770_3, c7_2770_4, c7_2770_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2783r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2783r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2783r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2783r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2783r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2783r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2784_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2783r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2784 :
    hubcapFit theRedpart rf7 p7_2783r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2784_1, c7_2784_2, c7_2784_3, c7_2784_4, c7_2784_5, c7_2784_6, c7_2784_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2783l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2785_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2783l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2785 :
    hubcapFit theRedpart rf7 p7_2783l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2785_1, c7_2785_2, c7_2785_3, c7_2785_4, c7_2785_5, c7_2785_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2781l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2781l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2781l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2781l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2781l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2787_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2781l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2787 :
    hubcapFit theRedpart rf7 p7_2781l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2787_1, c7_2787_2, c7_2787_3, c7_2787_4, c7_2787_5, c7_2787_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2780l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2789_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2780l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2789 :
    hubcapFit theRedpart rf7 p7_2780l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2789_1, c7_2789_2, c7_2789_3, c7_2789_4, c7_2789_5, c7_2789_6, c7_2789_7]

end FourColor

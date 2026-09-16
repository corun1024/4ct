import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 52 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2814l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2814l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2814l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2833_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2814l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2833 :
    hubcapFit theRedpart rf7 p7_2814l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2833_1, c7_2833_2, c7_2833_3, c7_2833_4, c7_2833_5, c7_2833_6, c7_2833_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2846_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2845r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2846_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2845r) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2846_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2845r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2846_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2845r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2846 :
    hubcapFit theRedpart rf7 p7_2845r
    (Hubcap.one 3 (-1) <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2846_1, c7_2846_2, c7_2846_3, c7_2846_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2847_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2845l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2847_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2845l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2847_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2845l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2847_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2845l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2847 :
    hubcapFit theRedpart rf7 p7_2845l
    (Hubcap.one 3 (-1) <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2847_1, c7_2847_2, c7_2847_3, c7_2847_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2850_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2849r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2850_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2849r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2850_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2849r) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2850_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2849r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2850 :
    hubcapFit theRedpart rf7 p7_2849r
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2850_1, c7_2850_2, c7_2850_3, c7_2850_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2851_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2849l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2851_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2849l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2851_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2849l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2851_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2849l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2851_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2849l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2851 :
    hubcapFit theRedpart rf7 p7_2849l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2851_1, c7_2851_2, c7_2851_3, c7_2851_4, c7_2851_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2853_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2843l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2853_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2843l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2853_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2853_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2843l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2853_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2843l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2853 :
    hubcapFit theRedpart rf7 p7_2843l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2853_1, c7_2853_2, c7_2853_3, c7_2853_4, c7_2853_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2855_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2855_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2855_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2855_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2842l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2855_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2842l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2855 :
    hubcapFit theRedpart rf7 p7_2842l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2855_1, c7_2855_2, c7_2855_3, c7_2855_4, c7_2855_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2860r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2860r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2860r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2860r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2860r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2861_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2860r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2861 :
    hubcapFit theRedpart rf7 p7_2860r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2861_1, c7_2861_2, c7_2861_3, c7_2861_4, c7_2861_5, c7_2861_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2862_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2860l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2862_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2860l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2862_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2860l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2862_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2860l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2862_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2860l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2862 :
    hubcapFit theRedpart rf7 p7_2860l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2862_1, c7_2862_2, c7_2862_3, c7_2862_4, c7_2862_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2864_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2859l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2864_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2859l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2864_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2859l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2864_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2859l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2864_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2859l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2864 :
    hubcapFit theRedpart rf7 p7_2859l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2864_1, c7_2864_2, c7_2864_3, c7_2864_4, c7_2864_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2866r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2866r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2866r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2866r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2866r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2867_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2866r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2867 :
    hubcapFit theRedpart rf7 p7_2866r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2867_1, c7_2867_2, c7_2867_3, c7_2867_4, c7_2867_5, c7_2867_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2866l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2866l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2866l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2866l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2866l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2868_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2866l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2868 :
    hubcapFit theRedpart rf7 p7_2866l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2868_1, c7_2868_2, c7_2868_3, c7_2868_4, c7_2868_5, c7_2868_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2870_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2865l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2870_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2865l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2870_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2865l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2870_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2865l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2870_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2865l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2870 :
    hubcapFit theRedpart rf7 p7_2865l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2870_1, c7_2870_2, c7_2870_3, c7_2870_4, c7_2870_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2857l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2857l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2857l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2857l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2857l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2872_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2857l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2872 :
    hubcapFit theRedpart rf7 p7_2857l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2872_1, c7_2872_2, c7_2872_3, c7_2872_4, c7_2872_5, c7_2872_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2873_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2873_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2873_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2856l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2873_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2856l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2873_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2856l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2873 :
    hubcapFit theRedpart rf7 p7_2856l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2873_1, c7_2873_2, c7_2873_3, c7_2873_4, c7_2873_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2878r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2878r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2878r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2878r) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2878r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2879_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2878r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2879 :
    hubcapFit theRedpart rf7 p7_2878r
    (Hubcap.one 3 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2879_1, c7_2879_2, c7_2879_3, c7_2879_4, c7_2879_5, c7_2879_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2878l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2878l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2878l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2878l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2878l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2880_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2878l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2880 :
    hubcapFit theRedpart rf7 p7_2878l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2880_1, c7_2880_2, c7_2880_3, c7_2880_4, c7_2880_5, c7_2880_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2876l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2876l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2876l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2876l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2876l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2882_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2876l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2882 :
    hubcapFit theRedpart rf7 p7_2876l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2882_1, c7_2882_2, c7_2882_3, c7_2882_4, c7_2882_5, c7_2882_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2887_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2886r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2887_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2886r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2887_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2886r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2887_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2886r) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2887_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2886r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2887 :
    hubcapFit theRedpart rf7 p7_2886r
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2887_1, c7_2887_2, c7_2887_3, c7_2887_4, c7_2887_5]

end FourColor

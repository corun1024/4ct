import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 54 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2938_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2936l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2938_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2936l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2938_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2936l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2938_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2936l) (hubSubn 7 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2938_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2936l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2938 :
    hubcapFit theRedpart rf7 p7_2936l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2938_1, c7_2938_2, c7_2938_3, c7_2938_4, c7_2938_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2935l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2935l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2935l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2935l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2940_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2935l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2940 :
    hubcapFit theRedpart rf7 p7_2935l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2940_1, c7_2940_2, c7_2940_3, c7_2940_4, c7_2940_5, c7_2940_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2934l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2934l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2934l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2941_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2934l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2941 :
    hubcapFit theRedpart rf7 p7_2934l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2941_1, c7_2941_2, c7_2941_3, c7_2941_4, c7_2941_5, c7_2941_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2910l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2910l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2910l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2943_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2910l) (hubSubn 7 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2943 :
    hubcapFit theRedpart rf7 p7_2910l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2943_1, c7_2943_2, c7_2943_3, c7_2943_4, c7_2943_5, c7_2943_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2945_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2909l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2945_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2909l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2945_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2909l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2945_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2909l) (hubSubn 7 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2945_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2909l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2945 :
    hubcapFit theRedpart rf7 p7_2909l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2945_1, c7_2945_2, c7_2945_3, c7_2945_4, c7_2945_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2908l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2908l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2908l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2908l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2908l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2908l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2946_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2908l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2946 :
    hubcapFit theRedpart rf7 p7_2908l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2946_1, c7_2946_2, c7_2946_3, c7_2946_4, c7_2946_5, c7_2946_6, c7_2946_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2959_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2958r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2959_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2958r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2959_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2958r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2959_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2958r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2959_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2958r) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2959 :
    hubcapFit theRedpart rf7 p7_2958r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2959_1, c7_2959_2, c7_2959_3, c7_2959_4, c7_2959_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2958l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2958l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2958l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2958l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2960_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2958l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2960 :
    hubcapFit theRedpart rf7 p7_2958l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2960_1, c7_2960_2, c7_2960_3, c7_2960_4, c7_2960_5, c7_2960_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2962_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2962_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2957l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2962_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2957l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2962_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2957l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2962_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2957l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2962 :
    hubcapFit theRedpart rf7 p7_2957l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2962_1, c7_2962_2, c7_2962_3, c7_2962_4, c7_2962_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2956l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2956l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2956l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2956l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2963_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2956l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2963 :
    hubcapFit theRedpart rf7 p7_2956l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2963_1, c7_2963_2, c7_2963_3, c7_2963_4, c7_2963_5, c7_2963_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2966_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2965r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2966_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2965r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2966_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2965r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2966_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2965r) (hubSubn 7 5 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2966_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2965r) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2966 :
    hubcapFit theRedpart rf7 p7_2965r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 5 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2966_1, c7_2966_2, c7_2966_3, c7_2966_4, c7_2966_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2965l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2965l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2967_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2965l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2967 :
    hubcapFit theRedpart rf7 p7_2965l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2967_1, c7_2967_2, c7_2967_3, c7_2967_4, c7_2967_5, c7_2967_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2969_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2954l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2969_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2954l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2969_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2954l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2969_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2954l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2969_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2954l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2969 :
    hubcapFit theRedpart rf7 p7_2954l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2969_1, c7_2969_2, c7_2969_3, c7_2969_4, c7_2969_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2971_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2971_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2953l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2971_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2953l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2971_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2953l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2971_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2953l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2971 :
    hubcapFit theRedpart rf7 p7_2953l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2971_1, c7_2971_2, c7_2971_3, c7_2971_4, c7_2971_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2979r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2979r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2979r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2979r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2979r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2980_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2979r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2980 :
    hubcapFit theRedpart rf7 p7_2979r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2980_1, c7_2980_2, c7_2980_3, c7_2980_4, c7_2980_5, c7_2980_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2981_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2979l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2981_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2979l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2981_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2979l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2981_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2979l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2981_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2979l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2981 :
    hubcapFit theRedpart rf7 p7_2979l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2981_1, c7_2981_2, c7_2981_3, c7_2981_4, c7_2981_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2977l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2977l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2977l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2983_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2977l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2983 :
    hubcapFit theRedpart rf7 p7_2977l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2983_1, c7_2983_2, c7_2983_3, c7_2983_4, c7_2983_5, c7_2983_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2976l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2976l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2976l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2976l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2976l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2976l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2985_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2976l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2985 :
    hubcapFit theRedpart rf7 p7_2976l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2985_1, c7_2985_2, c7_2985_3, c7_2985_4, c7_2985_5, c7_2985_6, c7_2985_7]

end FourColor

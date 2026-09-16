import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 62 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2947l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2947l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2947l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2947l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2947l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2947l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2947l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2948_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2947l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2948 :
    hubcapFit theRedpart rf9 p9_2947l
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2948_1, c9_2948_2, c9_2948_3, c9_2948_4, c9_2948_5, c9_2948_6, c9_2948_7, c9_2948_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2947r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2947r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2947r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2947r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2947r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2947r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2947r) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2950_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2947r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2950 :
    hubcapFit theRedpart rf9 p9_2947r
    (Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2950_1, c9_2950_2, c9_2950_3, c9_2950_4, c9_2950_5, c9_2950_6, c9_2950_7, c9_2950_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2959r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2959r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2959r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2959r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2959r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2959r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2960_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2959r) (hubSubn 9 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2960 :
    hubcapFit theRedpart rf9 p9_2959r
    (Hubcap.one 2 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2960_1, c9_2960_2, c9_2960_3, c9_2960_4, c9_2960_5, c9_2960_6, c9_2960_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2959l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2959l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2959l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2959l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2959l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2961_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2959l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2961 :
    hubcapFit theRedpart rf9 p9_2959l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2961_1, c9_2961_2, c9_2961_3, c9_2961_4, c9_2961_5, c9_2961_6, c9_2961_7, c9_2961_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2957l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2957l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2957l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2957l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2957l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2963_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2957l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2963 :
    hubcapFit theRedpart rf9 p9_2957l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2963_1, c9_2963_2, c9_2963_3, c9_2963_4, c9_2963_5, c9_2963_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2956l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2956l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2956l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2956l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2956l) (hubSubn 9 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2965_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2956l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2965 :
    hubcapFit theRedpart rf9 p9_2956l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2965_1, c9_2965_2, c9_2965_3, c9_2965_4, c9_2965_5, c9_2965_6, c9_2965_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2967r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2967r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2967r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2967r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2967r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2968_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2967r) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2968 :
    hubcapFit theRedpart rf9 p9_2967r
    (Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2968_1, c9_2968_2, c9_2968_3, c9_2968_4, c9_2968_5, c9_2968_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2967l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2967l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2967l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2967l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2967l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2969_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2967l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2969 :
    hubcapFit theRedpart rf9 p9_2967l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2969_1, c9_2969_2, c9_2969_3, c9_2969_4, c9_2969_5, c9_2969_6, c9_2969_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2972l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2972l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2972l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2972l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2972l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2972l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2972l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2973_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2972l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2973 :
    hubcapFit theRedpart rf9 p9_2972l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2973_1, c9_2973_2, c9_2973_3, c9_2973_4, c9_2973_5, c9_2973_6, c9_2973_7, c9_2973_8, c9_2973_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2975l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2975l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2975l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2975l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2975l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2975l) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2976_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2975l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2976 :
    hubcapFit theRedpart rf9 p9_2975l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2976_1, c9_2976_2, c9_2976_3, c9_2976_4, c9_2976_5, c9_2976_6, c9_2976_7, c9_2976_8, c9_2976_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2975r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2975r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2975r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2975r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2975r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_2975r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2975r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2975r) (hubSubn 9 5 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2978_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2975r) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2978 :
    hubcapFit theRedpart rf9 p9_2975r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 2 5 8 <|
     Hubcap.two 3 5 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2978_1, c9_2978_2, c9_2978_3, c9_2978_4, c9_2978_5, c9_2978_6, c9_2978_7, c9_2978_8, c9_2978_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2982r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2982r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2982r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2982r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2982r) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2983_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2982r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2983 :
    hubcapFit theRedpart rf9 p9_2982r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2983_1, c9_2983_2, c9_2983_3, c9_2983_4, c9_2983_5, c9_2983_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2982l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2982l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2982l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2982l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2982l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2982l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2982l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2984_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2982l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2984 :
    hubcapFit theRedpart rf9 p9_2982l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2984_1, c9_2984_2, c9_2984_3, c9_2984_4, c9_2984_5, c9_2984_6, c9_2984_7, c9_2984_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_2904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_2904l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_2904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_2904l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_2904l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_2904l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_2904l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_2986_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_2904l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_2986 :
    hubcapFit theRedpart rf9 p9_2904l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_2986_1, c9_2986_2, c9_2986_3, c9_2986_4, c9_2986_5, c9_2986_6, c9_2986_7, c9_2986_8]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 60 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3053l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3053l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3053l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3053l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3053l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3063_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3053l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3063 :
    hubcapFit theRedpart rf8 p8_3053l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3063_1, c8_3063_2, c8_3063_3, c8_3063_4, c8_3063_5, c8_3063_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3050l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3050l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3050l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3050l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3050l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3065_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3050l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3065 :
    hubcapFit theRedpart rf8 p8_3050l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3065_1, c8_3065_2, c8_3065_3, c8_3065_4, c8_3065_5, c8_3065_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3049l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3049l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3049l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3067_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3049l) (hubSubn 8 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3067 :
    hubcapFit theRedpart rf8 p8_3049l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3067_1, c8_3067_2, c8_3067_3, c8_3067_4, c8_3067_5, c8_3067_6, c8_3067_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3048l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3048l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3048l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3048l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3048l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3048l) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3069_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3048l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3069 :
    hubcapFit theRedpart rf8 p8_3048l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3069_1, c8_3069_2, c8_3069_3, c8_3069_4, c8_3069_5, c8_3069_6, c8_3069_7, c8_3069_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3081r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3081r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3081r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3081r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3081r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3081r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3081r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3082_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3081r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3082 :
    hubcapFit theRedpart rf8 p8_3081r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3082_1, c8_3082_2, c8_3082_3, c8_3082_4, c8_3082_5, c8_3082_6, c8_3082_7, c8_3082_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3081l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3081l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3081l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3081l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3083_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3081l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3083 :
    hubcapFit theRedpart rf8 p8_3081l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3083_1, c8_3083_2, c8_3083_3, c8_3083_4, c8_3083_5, c8_3083_6, c8_3083_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3080l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3080l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3080l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3080l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3085_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3080l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3085 :
    hubcapFit theRedpart rf8 p8_3080l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3085_1, c8_3085_2, c8_3085_3, c8_3085_4, c8_3085_5, c8_3085_6, c8_3085_7, c8_3085_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3079l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3079l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3079l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3079l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3087_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3079l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3087 :
    hubcapFit theRedpart rf8 p8_3079l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3087_1, c8_3087_2, c8_3087_3, c8_3087_4, c8_3087_5, c8_3087_6, c8_3087_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3077l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3077l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3077l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3077l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3077l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3089_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3077l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3089 :
    hubcapFit theRedpart rf8 p8_3077l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3089_1, c8_3089_2, c8_3089_3, c8_3089_4, c8_3089_5, c8_3089_6, c8_3089_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3074l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3074l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3074l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3074l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3074l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3074l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3091_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3074l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3091 :
    hubcapFit theRedpart rf8 p8_3074l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3091_1, c8_3091_2, c8_3091_3, c8_3091_4, c8_3091_5, c8_3091_6, c8_3091_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3073l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3073l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3073l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3073l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3073l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3073l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3093_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3073l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3093 :
    hubcapFit theRedpart rf8 p8_3073l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3093_1, c8_3093_2, c8_3093_3, c8_3093_4, c8_3093_5, c8_3093_6, c8_3093_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3072l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3072l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3072l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3072l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3072l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3095_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3072l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3095 :
    hubcapFit theRedpart rf8 p8_3072l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3095_1, c8_3095_2, c8_3095_3, c8_3095_4, c8_3095_5, c8_3095_6, c8_3095_7, c8_3095_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3071l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3071l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3071l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3071l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3071l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3071l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3071l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3097_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3071l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3097 :
    hubcapFit theRedpart rf8 p8_3071l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3097_1, c8_3097_2, c8_3097_3, c8_3097_4, c8_3097_5, c8_3097_6, c8_3097_7, c8_3097_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3099_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3099_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3045l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3099_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3045l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3099_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3045l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3099_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3045l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3099 :
    hubcapFit theRedpart rf8 p8_3045l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3099_1, c8_3099_2, c8_3099_3, c8_3099_4, c8_3099_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3101_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3043l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3101_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3043l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3101_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3043l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3101_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3043l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3101_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3043l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3101 :
    hubcapFit theRedpart rf8 p8_3043l
    (Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3101_1, c8_3101_2, c8_3101_3, c8_3101_4, c8_3101_5]

end FourColor

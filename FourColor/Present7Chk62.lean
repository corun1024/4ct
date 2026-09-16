import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 62 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3342_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3321l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3342_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3321l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3342_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3321l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3342_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3321l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3342_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3321l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3342 :
    hubcapFit theRedpart rf7 p7_3321l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3342_1, c7_3342_2, c7_3342_3, c7_3342_4, c7_3342_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3349_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3348r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3349_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3348r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3349_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3348r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3349_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3348r) (hubSubn 7 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3349_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3348r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3349 :
    hubcapFit theRedpart rf7 p7_3348r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 1 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3349_1, c7_3349_2, c7_3349_3, c7_3349_4, c7_3349_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3350_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3350_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3348l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3350_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3348l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3350_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3348l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3350_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3348l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3350 :
    hubcapFit theRedpart rf7 p7_3348l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3350_1, c7_3350_2, c7_3350_3, c7_3350_4, c7_3350_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3352_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3347l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3352_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3347l) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3352_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3347l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3352_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3347l) (hubSubn 7 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3352_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3347l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3352 :
    hubcapFit theRedpart rf7 p7_3347l
    (Hubcap.two 0 1 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3352_1, c7_3352_2, c7_3352_3, c7_3352_4, c7_3352_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3346l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3346l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3346l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3346l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3346l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3353_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3346l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3353 :
    hubcapFit theRedpart rf7 p7_3346l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3353_1, c7_3353_2, c7_3353_3, c7_3353_4, c7_3353_5, c7_3353_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3356r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3356r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3356r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3356r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3356r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3357_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3356r) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3357 :
    hubcapFit theRedpart rf7 p7_3356r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3357_1, c7_3357_2, c7_3357_3, c7_3357_4, c7_3357_5, c7_3357_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3358_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3356l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3358_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3356l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3358_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3356l) (hubSubn 7 4 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3358_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3356l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3358 :
    hubcapFit theRedpart rf7 p7_3356l
    (Hubcap.one 3 2 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 1 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3358_1, c7_3358_2, c7_3358_3, c7_3358_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3365r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3365r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3365r) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3365r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3365r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3366_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3365r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3366 :
    hubcapFit theRedpart rf7 p7_3365r
    (Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3366_1, c7_3366_2, c7_3366_3, c7_3366_4, c7_3366_5, c7_3366_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3365l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3365l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3365l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3365l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3365l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3367_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3365l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3367 :
    hubcapFit theRedpart rf7 p7_3365l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3367_1, c7_3367_2, c7_3367_3, c7_3367_4, c7_3367_5, c7_3367_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3369_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3364l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3369_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3364l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3369_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3364l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3369_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3364l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3369 :
    hubcapFit theRedpart rf7 p7_3364l
    (Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3369_1, c7_3369_2, c7_3369_3, c7_3369_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3363l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3363l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3363l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3363l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3370_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3363l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3370 :
    hubcapFit theRedpart rf7 p7_3363l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3370_1, c7_3370_2, c7_3370_3, c7_3370_4, c7_3370_5, c7_3370_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3372_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3362l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3372_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3362l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3372_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3372_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3362l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3372_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3362l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3372 :
    hubcapFit theRedpart rf7 p7_3362l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3372_1, c7_3372_2, c7_3372_3, c7_3372_4, c7_3372_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3373_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3361l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3373_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3361l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3373_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3361l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3373_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3361l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3373 :
    hubcapFit theRedpart rf7 p7_3361l
    (Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3373_1, c7_3373_2, c7_3373_3, c7_3373_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3360l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3360l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3360l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3360l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3360l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3375_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3360l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3375 :
    hubcapFit theRedpart rf7 p7_3360l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3375_1, c7_3375_2, c7_3375_3, c7_3375_4, c7_3375_5, c7_3375_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3387r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3387r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3387r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3387r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3388_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3387r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3388 :
    hubcapFit theRedpart rf7 p7_3387r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3388_1, c7_3388_2, c7_3388_3, c7_3388_4, c7_3388_5, c7_3388_6, c7_3388_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3394r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3394r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3394r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3394r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3394r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3395_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3394r) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3395 :
    hubcapFit theRedpart rf7 p7_3394r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3395_1, c7_3395_2, c7_3395_3, c7_3395_4, c7_3395_5, c7_3395_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3400r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3400r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3400r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3400r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3400r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3401_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3400r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3401 :
    hubcapFit theRedpart rf7 p7_3400r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3401_1, c7_3401_2, c7_3401_3, c7_3401_4, c7_3401_5, c7_3401_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3400l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3400l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3400l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3400l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3400l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3402_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3400l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3402 :
    hubcapFit theRedpart rf7 p7_3400l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3402_1, c7_3402_2, c7_3402_3, c7_3402_4, c7_3402_5, c7_3402_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3406r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3406r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3406r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3406r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3406r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3407_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3406r) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3407 :
    hubcapFit theRedpart rf7 p7_3406r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3407_1, c7_3407_2, c7_3407_3, c7_3407_4, c7_3407_5, c7_3407_6]

end FourColor

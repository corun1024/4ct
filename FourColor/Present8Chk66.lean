import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 66 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3328l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3328l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3328l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3328l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3328l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3328l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3344_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3328l) (hubSubn 8 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3344 :
    hubcapFit theRedpart rf8 p8_3328l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3344_1, c8_3344_2, c8_3344_3, c8_3344_4, c8_3344_5, c8_3344_6, c8_3344_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3346l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3346l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3346l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3346l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3346l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3347_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3346l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3347 :
    hubcapFit theRedpart rf8 p8_3346l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3347_1, c8_3347_2, c8_3347_3, c8_3347_4, c8_3347_5, c8_3347_6, c8_3347_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3346r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3346r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3346r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3346r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3346r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3346r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3349_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3346r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3349 :
    hubcapFit theRedpart rf8 p8_3346r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3349_1, c8_3349_2, c8_3349_3, c8_3349_4, c8_3349_5, c8_3349_6, c8_3349_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3319l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3319l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3319l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3319l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3319l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3319l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3353_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3319l) (hubSubn 8 5 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3353 :
    hubcapFit theRedpart rf8 p8_3319l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3353_1, c8_3353_2, c8_3353_3, c8_3353_4, c8_3353_5, c8_3353_6, c8_3353_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3363r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3363r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3363r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3363r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3363r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3364_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3363r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3364 :
    hubcapFit theRedpart rf8 p8_3363r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3364_1, c8_3364_2, c8_3364_3, c8_3364_4, c8_3364_5, c8_3364_6, c8_3364_7, c8_3364_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3363l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3363l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3363l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3363l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3363l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3365_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3363l) (hubSubn 8 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3365 :
    hubcapFit theRedpart rf8 p8_3363l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3365_1, c8_3365_2, c8_3365_3, c8_3365_4, c8_3365_5, c8_3365_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3362l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3362l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3362l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3362l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3367_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3362l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3367 :
    hubcapFit theRedpart rf8 p8_3362l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3367_1, c8_3367_2, c8_3367_3, c8_3367_4, c8_3367_5, c8_3367_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3360l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3360l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3360l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3360l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3360l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3360l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3369_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3360l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3369 :
    hubcapFit theRedpart rf8 p8_3360l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3369_1, c8_3369_2, c8_3369_3, c8_3369_4, c8_3369_5, c8_3369_6, c8_3369_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3359l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3359l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3359l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3359l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3371_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3359l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3371 :
    hubcapFit theRedpart rf8 p8_3359l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3371_1, c8_3371_2, c8_3371_3, c8_3371_4, c8_3371_5, c8_3371_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3358l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3358l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3358l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3358l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3358l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3358l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3372_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3358l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3372 :
    hubcapFit theRedpart rf8 p8_3358l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3372_1, c8_3372_2, c8_3372_3, c8_3372_4, c8_3372_5, c8_3372_6, c8_3372_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3357l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3357l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3357l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3357l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3357l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3357l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3374_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3357l) (hubSubn 8 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3374 :
    hubcapFit theRedpart rf8 p8_3357l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3374_1, c8_3374_2, c8_3374_3, c8_3374_4, c8_3374_5, c8_3374_6, c8_3374_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3392r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3392r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3392r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3392r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3392r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3392r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3392r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3393_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3392r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3393 :
    hubcapFit theRedpart rf8 p8_3392r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3393_1, c8_3393_2, c8_3393_3, c8_3393_4, c8_3393_5, c8_3393_6, c8_3393_7, c8_3393_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3392l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3394_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3392l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3394 :
    hubcapFit theRedpart rf8 p8_3392l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3394_1, c8_3394_2, c8_3394_3, c8_3394_4, c8_3394_5, c8_3394_6, c8_3394_7, c8_3394_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3391l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3391l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3391l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3391l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3391l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3396_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3391l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3396 :
    hubcapFit theRedpart rf8 p8_3391l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3396_1, c8_3396_2, c8_3396_3, c8_3396_4, c8_3396_5, c8_3396_6, c8_3396_7, c8_3396_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3399r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3399r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3399r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3399r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3399r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3399r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3400_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3399r) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3400 :
    hubcapFit theRedpart rf8 p8_3399r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3400_1, c8_3400_2, c8_3400_3, c8_3400_4, c8_3400_5, c8_3400_6, c8_3400_7]

end FourColor

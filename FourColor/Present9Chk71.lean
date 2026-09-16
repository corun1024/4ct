import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 71 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3329l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3329l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3329l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3329l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3360_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3329l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3360 :
    hubcapFit theRedpart rf9 p9_3329l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3360_1, c9_3360_2, c9_3360_3, c9_3360_4, c9_3360_5, c9_3360_6, c9_3360_7, c9_3360_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3328l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3328l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3328l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3328l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3328l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3362_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3328l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3362 :
    hubcapFit theRedpart rf9 p9_3328l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3362_1, c9_3362_2, c9_3362_3, c9_3362_4, c9_3362_5, c9_3362_6, c9_3362_7, c9_3362_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3327l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3327l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3327l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3327l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3327l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3364_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3327l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3364 :
    hubcapFit theRedpart rf9 p9_3327l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3364_1, c9_3364_2, c9_3364_3, c9_3364_4, c9_3364_5, c9_3364_6, c9_3364_7, c9_3364_8, c9_3364_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3326l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3326l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3326l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3326l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3326l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3326l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3366_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3326l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3366 :
    hubcapFit theRedpart rf9 p9_3326l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3366_1, c9_3366_2, c9_3366_3, c9_3366_4, c9_3366_5, c9_3366_6, c9_3366_7, c9_3366_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3325l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3325l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3325l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3325l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3325l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3368_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3325l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3368 :
    hubcapFit theRedpart rf9 p9_3325l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3368_1, c9_3368_2, c9_3368_3, c9_3368_4, c9_3368_5, c9_3368_6, c9_3368_7, c9_3368_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3383r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3383r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3383r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3383r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3383r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3383r) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3384_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3383r) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3384 :
    hubcapFit theRedpart rf9 p9_3383r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3384_1, c9_3384_2, c9_3384_3, c9_3384_4, c9_3384_5, c9_3384_6, c9_3384_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3388r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3388r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3388r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3388r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3388r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3388r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3389_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3388r) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3389 :
    hubcapFit theRedpart rf9 p9_3388r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3389_1, c9_3389_2, c9_3389_3, c9_3389_4, c9_3389_5, c9_3389_6, c9_3389_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3388l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3388l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3388l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3390_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3388l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3390 :
    hubcapFit theRedpart rf9 p9_3388l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3390_1, c9_3390_2, c9_3390_3, c9_3390_4, c9_3390_5, c9_3390_6, c9_3390_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3387l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3387l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3387l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3392_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3387l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3392 :
    hubcapFit theRedpart rf9 p9_3387l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3392_1, c9_3392_2, c9_3392_3, c9_3392_4, c9_3392_5, c9_3392_6, c9_3392_7, c9_3392_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3376l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3376l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3376l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3376l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3376l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3394_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3376l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3394 :
    hubcapFit theRedpart rf9 p9_3376l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3394_1, c9_3394_2, c9_3394_3, c9_3394_4, c9_3394_5, c9_3394_6, c9_3394_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3375l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3375l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3375l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3375l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3396_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3375l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3396 :
    hubcapFit theRedpart rf9 p9_3375l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3396_1, c9_3396_2, c9_3396_3, c9_3396_4, c9_3396_5, c9_3396_6, c9_3396_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3374l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3374l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3374l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3374l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3398_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3374l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3398 :
    hubcapFit theRedpart rf9 p9_3374l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3398_1, c9_3398_2, c9_3398_3, c9_3398_4, c9_3398_5, c9_3398_6, c9_3398_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3373l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3373l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3373l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3373l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3400_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3373l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3400 :
    hubcapFit theRedpart rf9 p9_3373l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3400_1, c9_3400_2, c9_3400_3, c9_3400_4, c9_3400_5, c9_3400_6, c9_3400_7, c9_3400_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3372l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3372l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3372l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3372l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3402_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3372l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3402 :
    hubcapFit theRedpart rf9 p9_3372l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3402_1, c9_3402_2, c9_3402_3, c9_3402_4, c9_3402_5, c9_3402_6, c9_3402_7, c9_3402_8, c9_3402_9]

end FourColor

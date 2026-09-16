import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 70 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3297l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3297l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3297l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3297l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3297l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3297l) (hubSubn 9 4 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3310_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3297l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3310 :
    hubcapFit theRedpart rf9 p9_3297l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 4 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3310_1, c9_3310_2, c9_3310_3, c9_3310_4, c9_3310_5, c9_3310_6, c9_3310_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3295l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3295l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3295l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3295l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3295l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3295l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3312_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3295l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3312 :
    hubcapFit theRedpart rf9 p9_3295l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3312_1, c9_3312_2, c9_3312_3, c9_3312_4, c9_3312_5, c9_3312_6, c9_3312_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3292l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3292l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3292l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3292l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3292l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3292l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3292l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3292l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3314_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3292l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3314 :
    hubcapFit theRedpart rf9 p9_3292l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3314_1, c9_3314_2, c9_3314_3, c9_3314_4, c9_3314_5, c9_3314_6, c9_3314_7, c9_3314_8, c9_3314_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3291l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3291l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3291l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3291l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3291l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3316_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3291l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3316 :
    hubcapFit theRedpart rf9 p9_3291l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3316_1, c9_3316_2, c9_3316_3, c9_3316_4, c9_3316_5, c9_3316_6, c9_3316_7, c9_3316_8, c9_3316_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3334r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3334r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3334r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3334r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3334r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3334r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3335_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3334r) (hubSubn 9 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3335 :
    hubcapFit theRedpart rf9 p9_3334r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3335_1, c9_3335_2, c9_3335_3, c9_3335_4, c9_3335_5, c9_3335_6, c9_3335_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3334l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3334l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3334l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3334l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3334l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3336_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3334l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3336 :
    hubcapFit theRedpart rf9 p9_3334l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3336_1, c9_3336_2, c9_3336_3, c9_3336_4, c9_3336_5, c9_3336_6, c9_3336_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3333l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3333l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3333l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3333l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3333l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3338_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3333l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3338 :
    hubcapFit theRedpart rf9 p9_3333l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3338_1, c9_3338_2, c9_3338_3, c9_3338_4, c9_3338_5, c9_3338_6, c9_3338_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3342r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3342r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3342r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3342r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3342r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3342r) (hubSubn 9 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3343_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3342r) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3343 :
    hubcapFit theRedpart rf9 p9_3342r
    (Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3343_1, c9_3343_2, c9_3343_3, c9_3343_4, c9_3343_5, c9_3343_6, c9_3343_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3342l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3342l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3342l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3342l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3342l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3344_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3342l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3344 :
    hubcapFit theRedpart rf9 p9_3342l
    (Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3344_1, c9_3344_2, c9_3344_3, c9_3344_4, c9_3344_5, c9_3344_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3341l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3341l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3341l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3341l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3341l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3346_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3341l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3346 :
    hubcapFit theRedpart rf9 p9_3341l
    (Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3346_1, c9_3346_2, c9_3346_3, c9_3346_4, c9_3346_5, c9_3346_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3340l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3340l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3340l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3340l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3347_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3340l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3347 :
    hubcapFit theRedpart rf9 p9_3340l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3347_1, c9_3347_2, c9_3347_3, c9_3347_4, c9_3347_5, c9_3347_6, c9_3347_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3352r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3352r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3352r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3352r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3353_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3352r) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3353 :
    hubcapFit theRedpart rf9 p9_3352r
    (Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3353_1, c9_3353_2, c9_3353_3, c9_3353_4, c9_3353_5, c9_3353_6, c9_3353_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3352l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3352l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3352l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3352l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3352l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3354_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3352l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3354 :
    hubcapFit theRedpart rf9 p9_3352l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3354_1, c9_3354_2, c9_3354_3, c9_3354_4, c9_3354_5, c9_3354_6, c9_3354_7, c9_3354_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3350l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3350l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3350l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3350l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3350l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3356_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3350l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3356 :
    hubcapFit theRedpart rf9 p9_3350l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3356_1, c9_3356_2, c9_3356_3, c9_3356_4, c9_3356_5, c9_3356_6, c9_3356_7, c9_3356_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3349l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3349l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3349l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3349l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3349l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3349l) (hubSubn 9 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3358_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3349l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3358 :
    hubcapFit theRedpart rf9 p9_3349l
    (Hubcap.one 1 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3358_1, c9_3358_2, c9_3358_3, c9_3358_4, c9_3358_5, c9_3358_6, c9_3358_7]

end FourColor

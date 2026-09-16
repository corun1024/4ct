import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 68 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3448l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3448l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3448l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3448l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3454_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3448l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3454 :
    hubcapFit theRedpart rf8 p8_3448l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3454_1, c8_3454_2, c8_3454_3, c8_3454_4, c8_3454_5, c8_3454_6, c8_3454_7, c8_3454_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3446l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3446l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3456_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3456 :
    hubcapFit theRedpart rf8 p8_3446l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3456_1, c8_3456_2, c8_3456_3, c8_3456_4, c8_3456_5, c8_3456_6, c8_3456_7, c8_3456_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3445l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3445l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3458_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3445l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3458 :
    hubcapFit theRedpart rf8 p8_3445l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3458_1, c8_3458_2, c8_3458_3, c8_3458_4, c8_3458_5, c8_3458_6, c8_3458_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3460_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3460 :
    hubcapFit theRedpart rf8 p8_3444l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3460_1, c8_3460_2, c8_3460_3, c8_3460_4, c8_3460_5, c8_3460_6, c8_3460_7, c8_3460_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3462_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3462_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3462_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3443l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3462_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3443l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3462_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3443l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3462 :
    hubcapFit theRedpart rf8 p8_3443l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3462_1, c8_3462_2, c8_3462_3, c8_3462_4, c8_3462_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3442l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3442l) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3463_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3442l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3463 :
    hubcapFit theRedpart rf8 p8_3442l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3463_1, c8_3463_2, c8_3463_3, c8_3463_4, c8_3463_5, c8_3463_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3441l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3441l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3441l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3441l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3441l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3465_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3441l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3465 :
    hubcapFit theRedpart rf8 p8_3441l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3465_1, c8_3465_2, c8_3465_3, c8_3465_4, c8_3465_5, c8_3465_6, c8_3465_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3467_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3438l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3467_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3438l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3467_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3438l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3467_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3438l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3467_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3438l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3467 :
    hubcapFit theRedpart rf8 p8_3438l
    (Hubcap.one 1 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3467_1, c8_3467_2, c8_3467_3, c8_3467_4, c8_3467_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3469_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3437l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3469_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3437l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3469_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3437l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3469_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3437l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3469_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3437l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3469 :
    hubcapFit theRedpart rf8 p8_3437l
    (Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3469_1, c8_3469_2, c8_3469_3, c8_3469_4, c8_3469_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3477r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3477r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3477r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3478_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3477r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3478 :
    hubcapFit theRedpart rf8 p8_3477r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3478_1, c8_3478_2, c8_3478_3, c8_3478_4, c8_3478_5, c8_3478_6, c8_3478_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3479_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3477l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3479 :
    hubcapFit theRedpart rf8 p8_3477l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3479_1, c8_3479_2, c8_3479_3, c8_3479_4, c8_3479_5, c8_3479_6, c8_3479_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3476l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3476l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3476l) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3481_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3476l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3481 :
    hubcapFit theRedpart rf8 p8_3476l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3481_1, c8_3481_2, c8_3481_3, c8_3481_4, c8_3481_5, c8_3481_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3482_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3475l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3482 :
    hubcapFit theRedpart rf8 p8_3475l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3482_1, c8_3482_2, c8_3482_3, c8_3482_4, c8_3482_5, c8_3482_6, c8_3482_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3474l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3474l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3484_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3474l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3484 :
    hubcapFit theRedpart rf8 p8_3474l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3484_1, c8_3484_2, c8_3484_3, c8_3484_4, c8_3484_5, c8_3484_6, c8_3484_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3473l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3473l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3486_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3473l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3486 :
    hubcapFit theRedpart rf8 p8_3473l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3486_1, c8_3486_2, c8_3486_3, c8_3486_4, c8_3486_5, c8_3486_6, c8_3486_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3488_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3472l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3488 :
    hubcapFit theRedpart rf8 p8_3472l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3488_1, c8_3488_2, c8_3488_3, c8_3488_4, c8_3488_5, c8_3488_6, c8_3488_7]

end FourColor

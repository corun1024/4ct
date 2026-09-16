import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 73 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3439l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3439l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3439l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3439l) (hubSubn 9 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3439l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3456_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3439l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3456 :
    hubcapFit theRedpart rf9 p9_3439l
    (Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3456_1, c9_3456_2, c9_3456_3, c9_3456_4, c9_3456_5, c9_3456_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3438l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3438l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3438l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3438l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3438l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3438l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3438l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3438l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3458_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3438l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3458 :
    hubcapFit theRedpart rf9 p9_3438l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3458_1, c9_3458_2, c9_3458_3, c9_3458_4, c9_3458_5, c9_3458_6, c9_3458_7, c9_3458_8, c9_3458_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3415l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3415l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3415l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3415l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3415l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3460_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3415l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3460 :
    hubcapFit theRedpart rf9 p9_3415l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3460_1, c9_3460_2, c9_3460_3, c9_3460_4, c9_3460_5, c9_3460_6, c9_3460_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3467r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3467r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3467r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3467r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3467r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3467r) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3468_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3467r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3468 :
    hubcapFit theRedpart rf9 p9_3467r
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3468_1, c9_3468_2, c9_3468_3, c9_3468_4, c9_3468_5, c9_3468_6, c9_3468_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3467l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3467l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3467l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3467l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3467l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3467l) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3469_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3467l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3469 :
    hubcapFit theRedpart rf9 p9_3467l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3469_1, c9_3469_2, c9_3469_3, c9_3469_4, c9_3469_5, c9_3469_6, c9_3469_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3464l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3464l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3464l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3464l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3471_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3464l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3471 :
    hubcapFit theRedpart rf9 p9_3464l
    (Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3471_1, c9_3471_2, c9_3471_3, c9_3471_4, c9_3471_5, c9_3471_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3463l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3463l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3463l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3463l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3463l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3473_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3473 :
    hubcapFit theRedpart rf9 p9_3463l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3473_1, c9_3473_2, c9_3473_3, c9_3473_4, c9_3473_5, c9_3473_6, c9_3473_7, c9_3473_8, c9_3473_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3462l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3462l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3462l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3462l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3462l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3475_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3462l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3475 :
    hubcapFit theRedpart rf9 p9_3462l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3475_1, c9_3475_2, c9_3475_3, c9_3475_4, c9_3475_5, c9_3475_6, c9_3475_7, c9_3475_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3413l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3413l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3477_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3477 :
    hubcapFit theRedpart rf9 p9_3413l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3477_1, c9_3477_2, c9_3477_3, c9_3477_4, c9_3477_5, c9_3477_6, c9_3477_7, c9_3477_8, c9_3477_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3412l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3412l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3412l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3412l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3412l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3479_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3412l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3479 :
    hubcapFit theRedpart rf9 p9_3412l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3479_1, c9_3479_2, c9_3479_3, c9_3479_4, c9_3479_5, c9_3479_6, c9_3479_7, c9_3479_8, c9_3479_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3411l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3411l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3411l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3411l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3411l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3481_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3411l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3481 :
    hubcapFit theRedpart rf9 p9_3411l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3481_1, c9_3481_2, c9_3481_3, c9_3481_4, c9_3481_5, c9_3481_6, c9_3481_7, c9_3481_8, c9_3481_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3492r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3492r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3492r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3492r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3492r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3492r) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3493_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3492r) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3493 :
    hubcapFit theRedpart rf9 p9_3492r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3493_1, c9_3493_2, c9_3493_3, c9_3493_4, c9_3493_5, c9_3493_6, c9_3493_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3492l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3492l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3492l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3492l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3492l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3492l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3494_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3492l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3494 :
    hubcapFit theRedpart rf9 p9_3492l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3494_1, c9_3494_2, c9_3494_3, c9_3494_4, c9_3494_5, c9_3494_6, c9_3494_7, c9_3494_8, c9_3494_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3490l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3490l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3490l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3490l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3490l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3490l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3496_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3490l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3496 :
    hubcapFit theRedpart rf9 p9_3490l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3496_1, c9_3496_2, c9_3496_3, c9_3496_4, c9_3496_5, c9_3496_6, c9_3496_7, c9_3496_8, c9_3496_9]

end FourColor

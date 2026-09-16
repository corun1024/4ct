import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 74 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3489l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3489l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3489l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3489l) (hubSubn 9 8 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3498_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3489l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3498 :
    hubcapFit theRedpart rf9 p9_3489l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3498_1, c9_3498_2, c9_3498_3, c9_3498_4, c9_3498_5, c9_3498_6, c9_3498_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3488l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3488l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3488l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3500_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3500 :
    hubcapFit theRedpart rf9 p9_3488l
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
  simp [hubcapFit, c9_3500_1, c9_3500_2, c9_3500_3, c9_3500_4, c9_3500_5, c9_3500_6, c9_3500_7, c9_3500_8, c9_3500_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3487l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3487l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3487l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3487l) (hubSubn 9 8 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3502_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3487l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3502 :
    hubcapFit theRedpart rf9 p9_3487l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3502_1, c9_3502_2, c9_3502_3, c9_3502_4, c9_3502_5, c9_3502_6, c9_3502_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3486l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3486l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3486l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3486l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3486l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3486l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3486l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3504_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3486l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3504 :
    hubcapFit theRedpart rf9 p9_3486l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3504_1, c9_3504_2, c9_3504_3, c9_3504_4, c9_3504_5, c9_3504_6, c9_3504_7, c9_3504_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3485l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3485l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3485l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3485l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3485l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3485l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3485l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3506_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3485l) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3506 :
    hubcapFit theRedpart rf9 p9_3485l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3506_1, c9_3506_2, c9_3506_3, c9_3506_4, c9_3506_5, c9_3506_6, c9_3506_7, c9_3506_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3484l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3484l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3484l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3508_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3484l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3508 :
    hubcapFit theRedpart rf9 p9_3484l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3508_1, c9_3508_2, c9_3508_3, c9_3508_4, c9_3508_5, c9_3508_6, c9_3508_7, c9_3508_8, c9_3508_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3520r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3520r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3520r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3520r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3520r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3520r) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3521_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3520r) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3521 :
    hubcapFit theRedpart rf9 p9_3520r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3521_1, c9_3521_2, c9_3521_3, c9_3521_4, c9_3521_5, c9_3521_6, c9_3521_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3520l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3520l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3520l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3520l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3520l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3520l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3520l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3522_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3520l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3522 :
    hubcapFit theRedpart rf9 p9_3520l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3522_1, c9_3522_2, c9_3522_3, c9_3522_4, c9_3522_5, c9_3522_6, c9_3522_7, c9_3522_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3519l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3519l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3519l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3519l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3519l) (hubSubn 9 8 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3524_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3519l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3524 :
    hubcapFit theRedpart rf9 p9_3519l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3524_1, c9_3524_2, c9_3524_3, c9_3524_4, c9_3524_5, c9_3524_6, c9_3524_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3517l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3517l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3517l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3526_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3517l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3526 :
    hubcapFit theRedpart rf9 p9_3517l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3526_1, c9_3526_2, c9_3526_3, c9_3526_4, c9_3526_5, c9_3526_6, c9_3526_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3516l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3516l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3516l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3516l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3516l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3528_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3516l) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3528 :
    hubcapFit theRedpart rf9 p9_3516l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3528_1, c9_3528_2, c9_3528_3, c9_3528_4, c9_3528_5, c9_3528_6, c9_3528_7, c9_3528_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3530r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3530r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3530r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3530r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3530r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3530r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3530r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3531_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3530r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3531 :
    hubcapFit theRedpart rf9 p9_3530r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3531_1, c9_3531_2, c9_3531_3, c9_3531_4, c9_3531_5, c9_3531_6, c9_3531_7, c9_3531_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3530l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3530l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3530l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3530l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3530l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3530l) (hubSubn 9 8 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3532_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3530l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3532 :
    hubcapFit theRedpart rf9 p9_3530l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3532_1, c9_3532_2, c9_3532_3, c9_3532_4, c9_3532_5, c9_3532_6, c9_3532_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3512l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3512l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3512l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3512l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3512l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3512l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3512l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3534_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3512l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3534 :
    hubcapFit theRedpart rf9 p9_3512l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3534_1, c9_3534_2, c9_3534_3, c9_3534_4, c9_3534_5, c9_3534_6, c9_3534_7, c9_3534_8, c9_3534_9]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 11 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_477l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_482_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_482 :
    hubcapFit theRedpart rf9 p9_477l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_482_1, c9_482_2, c9_482_3, c9_482_4, c9_482_5, c9_482_6, c9_482_7, c9_482_8, c9_482_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_476l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_476l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_476l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_476l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_476l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_484_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_476l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_484 :
    hubcapFit theRedpart rf9 p9_476l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_484_1, c9_484_2, c9_484_3, c9_484_4, c9_484_5, c9_484_6, c9_484_7, c9_484_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_475l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_475l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_475l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_486_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_475l) (hubSubn 9 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_486 :
    hubcapFit theRedpart rf9 p9_475l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_486_1, c9_486_2, c9_486_3, c9_486_4, c9_486_5, c9_486_6, c9_486_7, c9_486_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_489r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_489r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_489r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_489r) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_489r) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_490_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_489r) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_490 :
    hubcapFit theRedpart rf9 p9_489r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_490_1, c9_490_2, c9_490_3, c9_490_4, c9_490_5, c9_490_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_489l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_489l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_491_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_489l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_491 :
    hubcapFit theRedpart rf9 p9_489l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_491_1, c9_491_2, c9_491_3, c9_491_4, c9_491_5, c9_491_6, c9_491_7, c9_491_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_488l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_488l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_493_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_488l) (hubSubn 9 8 7) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_493 :
    hubcapFit theRedpart rf9 p9_488l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 7 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_493_1, c9_493_2, c9_493_3, c9_493_4, c9_493_5, c9_493_6, c9_493_7, c9_493_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_509r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_509r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_509r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_509r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_509r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_509r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_509r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_510_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_509r) (hubSubn 9 8 7) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_510 :
    hubcapFit theRedpart rf9 p9_509r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.two 7 8 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_510_1, c9_510_2, c9_510_3, c9_510_4, c9_510_5, c9_510_6, c9_510_7, c9_510_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_509l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_509l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_509l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_509l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_509l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_509l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_509l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_511_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_509l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_511 :
    hubcapFit theRedpart rf9 p9_509l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_511_1, c9_511_2, c9_511_3, c9_511_4, c9_511_5, c9_511_6, c9_511_7, c9_511_8, c9_511_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_507l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_507l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_507l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_507l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_507l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_507l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_507l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_513_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_507l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_513 :
    hubcapFit theRedpart rf9 p9_507l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_513_1, c9_513_2, c9_513_3, c9_513_4, c9_513_5, c9_513_6, c9_513_7, c9_513_8, c9_513_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_505l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_505l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_515_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_505l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_515 :
    hubcapFit theRedpart rf9 p9_505l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_515_1, c9_515_2, c9_515_3, c9_515_4, c9_515_5, c9_515_6, c9_515_7, c9_515_8, c9_515_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_504l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_504l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_504l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_504l) (hubSubn 9 2 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_517_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_504l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_517 :
    hubcapFit theRedpart rf9 p9_504l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 2 <|
     Hubcap.two 1 2 8 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_517_1, c9_517_2, c9_517_3, c9_517_4, c9_517_5, c9_517_6, c9_517_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_503l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_503l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_503l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_503l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_503l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_503l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_503l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_519_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_503l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_519 :
    hubcapFit theRedpart rf9 p9_503l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 2 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_519_1, c9_519_2, c9_519_3, c9_519_4, c9_519_5, c9_519_6, c9_519_7, c9_519_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_502l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_502l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_502l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_502l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_502l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_502l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_502l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_521_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_502l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_521 :
    hubcapFit theRedpart rf9 p9_502l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_521_1, c9_521_2, c9_521_3, c9_521_4, c9_521_5, c9_521_6, c9_521_7, c9_521_8]

end FourColor

import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 72 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3371l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3371l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3371l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3371l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3404_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3371l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3404 :
    hubcapFit theRedpart rf9 p9_3371l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3404_1, c9_3404_2, c9_3404_3, c9_3404_4, c9_3404_5, c9_3404_6, c9_3404_7, c9_3404_8, c9_3404_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3370l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3370l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3370l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3370l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3406_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3370l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3406 :
    hubcapFit theRedpart rf9 p9_3370l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3406_1, c9_3406_2, c9_3406_3, c9_3406_4, c9_3406_5, c9_3406_6, c9_3406_7, c9_3406_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3426r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3426r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3426r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3426r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3426r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3426r) (hubSubn 9 7 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3427_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3426r) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3427 :
    hubcapFit theRedpart rf9 p9_3426r
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3427_1, c9_3427_2, c9_3427_3, c9_3427_4, c9_3427_5, c9_3427_6, c9_3427_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3426l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3426l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3426l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3428_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3426l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3428 :
    hubcapFit theRedpart rf9 p9_3426l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3428_1, c9_3428_2, c9_3428_3, c9_3428_4, c9_3428_5, c9_3428_6, c9_3428_7, c9_3428_8, c9_3428_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3425l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3425l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3425l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3425l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3425l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3430_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3425l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3430 :
    hubcapFit theRedpart rf9 p9_3425l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3430_1, c9_3430_2, c9_3430_3, c9_3430_4, c9_3430_5, c9_3430_6, c9_3430_7, c9_3430_8, c9_3430_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3424l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3424l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3424l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3424l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3432_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3424l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3432 :
    hubcapFit theRedpart rf9 p9_3424l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3432_1, c9_3432_2, c9_3432_3, c9_3432_4, c9_3432_5, c9_3432_6, c9_3432_7, c9_3432_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3421l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3421l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3421l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3421l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3421l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3421l) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3434_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3421l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3434 :
    hubcapFit theRedpart rf9 p9_3421l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3434_1, c9_3434_2, c9_3434_3, c9_3434_4, c9_3434_5, c9_3434_6, c9_3434_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3418l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3418l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3418l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3436_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3418l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3436 :
    hubcapFit theRedpart rf9 p9_3418l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3436_1, c9_3436_2, c9_3436_3, c9_3436_4, c9_3436_5, c9_3436_6, c9_3436_7, c9_3436_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3446r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3446r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3446r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3446r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3446r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3446r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3446r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3447_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3446r) (hubSubn 9 7 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3447 :
    hubcapFit theRedpart rf9 p9_3446r
    (Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3447_1, c9_3447_2, c9_3447_3, c9_3447_4, c9_3447_5, c9_3447_6, c9_3447_7, c9_3447_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3446l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3446l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3446l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3446l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3448_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3446l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3448 :
    hubcapFit theRedpart rf9 p9_3446l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3448_1, c9_3448_2, c9_3448_3, c9_3448_4, c9_3448_5, c9_3448_6, c9_3448_7, c9_3448_8, c9_3448_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3444l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3450_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3450 :
    hubcapFit theRedpart rf9 p9_3444l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3450_1, c9_3450_2, c9_3450_3, c9_3450_4, c9_3450_5, c9_3450_6, c9_3450_7, c9_3450_8, c9_3450_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3443l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3443l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3443l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3452_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3452 :
    hubcapFit theRedpart rf9 p9_3443l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3452_1, c9_3452_2, c9_3452_3, c9_3452_4, c9_3452_5, c9_3452_6, c9_3452_7, c9_3452_8, c9_3452_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3454_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3454 :
    hubcapFit theRedpart rf9 p9_3442l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3454_1, c9_3454_2, c9_3454_3, c9_3454_4, c9_3454_5, c9_3454_6, c9_3454_7, c9_3454_8, c9_3454_9]

end FourColor

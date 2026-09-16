import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 69 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3491l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3491l) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3491l) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3491l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3491l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3492_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3491l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3492 :
    hubcapFit theRedpart rf8 p8_3491l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3492_1, c8_3492_2, c8_3492_3, c8_3492_4, c8_3492_5, c8_3492_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3491r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3491r) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3491r) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3491r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3491r) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3494_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3491r) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3494 :
    hubcapFit theRedpart rf8 p8_3491r
    (Hubcap.one 3 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3494_1, c8_3494_2, c8_3494_3, c8_3494_4, c8_3494_5, c8_3494_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3497l) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3497l) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3497l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3497l) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3498_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3497l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3498 :
    hubcapFit theRedpart rf8 p8_3497l
    (Hubcap.one 2 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3498_1, c8_3498_2, c8_3498_3, c8_3498_4, c8_3498_5, c8_3498_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3497r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3497r) (hubSubn 8 5 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3497r) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3497r) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3497r) (hubSubn 8 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3500_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3497r) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3500 :
    hubcapFit theRedpart rf8 p8_3497r
    (Hubcap.one 2 0 <|
     Hubcap.two 0 5 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3500_1, c8_3500_2, c8_3500_3, c8_3500_4, c8_3500_5, c8_3500_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3528r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3528r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3528r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3528r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3528r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3528r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3529_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3528r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3529 :
    hubcapFit theRedpart rf8 p8_3528r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3529_1, c8_3529_2, c8_3529_3, c8_3529_4, c8_3529_5, c8_3529_6, c8_3529_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3528l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3530_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3528l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3530 :
    hubcapFit theRedpart rf8 p8_3528l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3530_1, c8_3530_2, c8_3530_3, c8_3530_4, c8_3530_5, c8_3530_6, c8_3530_7, c8_3530_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3527l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3527l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3527l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3532_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3527l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3532 :
    hubcapFit theRedpart rf8 p8_3527l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3532_1, c8_3532_2, c8_3532_3, c8_3532_4, c8_3532_5, c8_3532_6, c8_3532_7, c8_3532_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3526l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3526l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3534_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3526l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3534 :
    hubcapFit theRedpart rf8 p8_3526l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3534_1, c8_3534_2, c8_3534_3, c8_3534_4, c8_3534_5, c8_3534_6, c8_3534_7, c8_3534_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3525l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3525l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3525l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3536_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3525l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3536 :
    hubcapFit theRedpart rf8 p8_3525l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3536_1, c8_3536_2, c8_3536_3, c8_3536_4, c8_3536_5, c8_3536_6, c8_3536_7, c8_3536_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3524l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3524l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3524l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3524l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3524l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3538_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3524l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3538 :
    hubcapFit theRedpart rf8 p8_3524l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3538_1, c8_3538_2, c8_3538_3, c8_3538_4, c8_3538_5, c8_3538_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3523l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3523l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3523l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3539_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3523l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3539 :
    hubcapFit theRedpart rf8 p8_3523l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3539_1, c8_3539_2, c8_3539_3, c8_3539_4, c8_3539_5, c8_3539_6, c8_3539_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3522l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3522l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3522l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3522l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3541_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3522l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3541 :
    hubcapFit theRedpart rf8 p8_3522l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3541_1, c8_3541_2, c8_3541_3, c8_3541_4, c8_3541_5, c8_3541_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3520l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3520l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3520l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3520l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3520l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3543_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3520l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3543 :
    hubcapFit theRedpart rf8 p8_3520l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3543_1, c8_3543_2, c8_3543_3, c8_3543_4, c8_3543_5, c8_3543_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3544_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3519l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3544_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3519l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3544_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3519l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3544_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3519l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3544_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3519l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3544 :
    hubcapFit theRedpart rf8 p8_3519l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3544_1, c8_3544_2, c8_3544_3, c8_3544_4, c8_3544_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3517l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3517l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3517l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3517l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3546_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3517l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3546 :
    hubcapFit theRedpart rf8 p8_3517l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3546_1, c8_3546_2, c8_3546_3, c8_3546_4, c8_3546_5, c8_3546_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3515l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3515l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3515l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3515l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3515l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3548_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3515l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3548 :
    hubcapFit theRedpart rf8 p8_3515l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3548_1, c8_3548_2, c8_3548_3, c8_3548_4, c8_3548_5, c8_3548_6]

end FourColor

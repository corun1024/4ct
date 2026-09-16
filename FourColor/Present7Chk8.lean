import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 8 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_478l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_478l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_478l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_478l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_478l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_480_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_478l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_480 :
    hubcapFit theRedpart rf7 p7_478l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_480_1, c7_480_2, c7_480_3, c7_480_4, c7_480_5, c7_480_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_477l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_477l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_477l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_477l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_477l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_482_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_477l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_482 :
    hubcapFit theRedpart rf7 p7_477l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_482_1, c7_482_2, c7_482_3, c7_482_4, c7_482_5, c7_482_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_476l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_476l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_476l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_483_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_476l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_483 :
    hubcapFit theRedpart rf7 p7_476l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_483_1, c7_483_2, c7_483_3, c7_483_4, c7_483_5, c7_483_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_485_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_475l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_485_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_475l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_485_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_475l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_485_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_475l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_485_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_475l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_485 :
    hubcapFit theRedpart rf7 p7_475l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_485_1, c7_485_2, c7_485_3, c7_485_4, c7_485_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_486_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_474l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_486_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_474l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_486_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_474l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_486_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_474l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_486_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_474l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_486 :
    hubcapFit theRedpart rf7 p7_474l
    (Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_486_1, c7_486_2, c7_486_3, c7_486_4, c7_486_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_488_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_488_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_473l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_488_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_473l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_488_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_473l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_488_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_473l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_488 :
    hubcapFit theRedpart rf7 p7_473l
    (Hubcap.one 0 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_488_1, c7_488_2, c7_488_3, c7_488_4, c7_488_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_472l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_472l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_472l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_472l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_472l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_489_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_472l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_489 :
    hubcapFit theRedpart rf7 p7_472l
    (Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_489_1, c7_489_2, c7_489_3, c7_489_4, c7_489_5, c7_489_6, c7_489_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_471l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_471l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_491_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_471l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_491 :
    hubcapFit theRedpart rf7 p7_471l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_491_1, c7_491_2, c7_491_3, c7_491_4, c7_491_5, c7_491_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_498r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_498r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_498r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_498r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_498r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_498r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_499_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_498r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_499 :
    hubcapFit theRedpart rf7 p7_498r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_499_1, c7_499_2, c7_499_3, c7_499_4, c7_499_5, c7_499_6, c7_499_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_500_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_498l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_500_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_498l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_500_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_498l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_500_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_498l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_500_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_498l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_500 :
    hubcapFit theRedpart rf7 p7_498l
    (Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_500_1, c7_500_2, c7_500_3, c7_500_4, c7_500_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_502_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_502_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_497l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_502_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_502_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_497l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_502_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_497l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_502 :
    hubcapFit theRedpart rf7 p7_497l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_502_1, c7_502_2, c7_502_3, c7_502_4, c7_502_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_503_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_496l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_503_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_496l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_503_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_496l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_503_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_496l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_503_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_496l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_503 :
    hubcapFit theRedpart rf7 p7_496l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_503_1, c7_503_2, c7_503_3, c7_503_4, c7_503_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_505_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_495l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_505_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_495l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_505_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_495l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_505_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_495l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_505_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_495l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_505 :
    hubcapFit theRedpart rf7 p7_495l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_505_1, c7_505_2, c7_505_3, c7_505_4, c7_505_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_494l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_494l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_494l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_494l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_494l) (hubSubn 7 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_494l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_506_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_494l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_506 :
    hubcapFit theRedpart rf7 p7_494l
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_506_1, c7_506_2, c7_506_3, c7_506_4, c7_506_5, c7_506_6, c7_506_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_493l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_493l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_508_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_493l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_508 :
    hubcapFit theRedpart rf7 p7_493l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_508_1, c7_508_2, c7_508_3, c7_508_4, c7_508_5, c7_508_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_512r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_512r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_512r) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_512r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_512r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_513_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_512r) (hubSubn 7 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_513 :
    hubcapFit theRedpart rf7 p7_512r
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_513_1, c7_513_2, c7_513_3, c7_513_4, c7_513_5, c7_513_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_512l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_512l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_512l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_512l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_514_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_512l) (hubSubn 7 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_514 :
    hubcapFit theRedpart rf7 p7_512l
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_514_1, c7_514_2, c7_514_3, c7_514_4, c7_514_5, c7_514_6, c7_514_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_511l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_511l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_511l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_516_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_516 :
    hubcapFit theRedpart rf7 p7_511l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_516_1, c7_516_2, c7_516_3, c7_516_4, c7_516_5, c7_516_6, c7_516_7]

end FourColor

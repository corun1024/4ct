import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 64 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3480l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3480l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3480l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3480l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3480l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3480l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3482_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3480l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3482 :
    hubcapFit theRedpart rf7 p7_3480l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3482_1, c7_3482_2, c7_3482_3, c7_3482_4, c7_3482_5, c7_3482_6, c7_3482_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3479l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3479l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3479l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3479l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3479l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3484_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3479l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3484 :
    hubcapFit theRedpart rf7 p7_3479l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3484_1, c7_3484_2, c7_3484_3, c7_3484_4, c7_3484_5, c7_3484_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3477l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3477l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3477l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3486_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3477l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3486 :
    hubcapFit theRedpart rf7 p7_3477l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3486_1, c7_3486_2, c7_3486_3, c7_3486_4, c7_3486_5, c7_3486_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3476l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3476l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3476l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3487_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3476l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3487 :
    hubcapFit theRedpart rf7 p7_3476l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3487_1, c7_3487_2, c7_3487_3, c7_3487_4, c7_3487_5, c7_3487_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3475l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3475l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3475l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3475l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3489_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3475l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3489 :
    hubcapFit theRedpart rf7 p7_3475l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3489_1, c7_3489_2, c7_3489_3, c7_3489_4, c7_3489_5, c7_3489_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3474l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3474l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3474l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3490_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3474l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3490 :
    hubcapFit theRedpart rf7 p7_3474l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3490_1, c7_3490_2, c7_3490_3, c7_3490_4, c7_3490_5, c7_3490_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3492_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3492_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3492_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3473l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3492_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3473l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3492_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3473l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3492 :
    hubcapFit theRedpart rf7 p7_3473l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3492_1, c7_3492_2, c7_3492_3, c7_3492_4, c7_3492_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3493_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3493_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3472l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3493_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3472l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3493_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3472l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3493_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3472l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3493 :
    hubcapFit theRedpart rf7 p7_3472l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3493_1, c7_3493_2, c7_3493_3, c7_3493_4, c7_3493_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3495_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3471l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3495_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3471l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3495_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3471l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3495_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3471l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3495_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3471l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3495 :
    hubcapFit theRedpart rf7 p7_3471l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3495_1, c7_3495_2, c7_3495_3, c7_3495_4, c7_3495_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3500_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3499r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3500_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3499r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3500_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3499r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3500_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3499r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3500_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3499r) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3500 :
    hubcapFit theRedpart rf7 p7_3499r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3500_1, c7_3500_2, c7_3500_3, c7_3500_4, c7_3500_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3499l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3499l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3499l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3501_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3499l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3501 :
    hubcapFit theRedpart rf7 p7_3499l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 1 3 3 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3501_1, c7_3501_2, c7_3501_3, c7_3501_4, c7_3501_5, c7_3501_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3503_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3503_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3498l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3503_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3498l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3503_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3498l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3503_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3498l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3503 :
    hubcapFit theRedpart rf7 p7_3498l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 1 5 2 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3503_1, c7_3503_2, c7_3503_3, c7_3503_4, c7_3503_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3504_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3504_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3504_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3504_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3497l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3504_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3497l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3504 :
    hubcapFit theRedpart rf7 p7_3497l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3504_1, c7_3504_2, c7_3504_3, c7_3504_4, c7_3504_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3506_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3463l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3506_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3463l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3506_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3463l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3506_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3463l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3506_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3463l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3506 :
    hubcapFit theRedpart rf7 p7_3463l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3506_1, c7_3506_2, c7_3506_3, c7_3506_4, c7_3506_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3513r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3513r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3513r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3513r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3513r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3513r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3514_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3513r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3514 :
    hubcapFit theRedpart rf7 p7_3513r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3514_1, c7_3514_2, c7_3514_3, c7_3514_4, c7_3514_5, c7_3514_6, c7_3514_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3513l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3513l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3513l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3513l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3513l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3515_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3513l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3515 :
    hubcapFit theRedpart rf7 p7_3513l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3515_1, c7_3515_2, c7_3515_3, c7_3515_4, c7_3515_5, c7_3515_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3517_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3512l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3517_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3517_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3512l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3517_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3512l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3517_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3512l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3517 :
    hubcapFit theRedpart rf7 p7_3512l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3517_1, c7_3517_2, c7_3517_3, c7_3517_4, c7_3517_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3518_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3511l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3518_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3518_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3511l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3518_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3511l) (hubSubn 7 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3518_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3511l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3518 :
    hubcapFit theRedpart rf7 p7_3511l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3518_1, c7_3518_2, c7_3518_3, c7_3518_4, c7_3518_5]

end FourColor

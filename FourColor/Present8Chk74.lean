import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 74 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3744l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3744l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3744l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3749_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3744l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3749 :
    hubcapFit theRedpart rf8 p8_3744l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3749_1, c8_3749_2, c8_3749_3, c8_3749_4, c8_3749_5, c8_3749_6, c8_3749_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3743l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3743l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3743l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3751_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3743l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3751 :
    hubcapFit theRedpart rf8 p8_3743l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3751_1, c8_3751_2, c8_3751_3, c8_3751_4, c8_3751_5, c8_3751_6, c8_3751_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3742l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3742l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3742l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3753_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3742l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3753 :
    hubcapFit theRedpart rf8 p8_3742l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3753_1, c8_3753_2, c8_3753_3, c8_3753_4, c8_3753_5, c8_3753_6, c8_3753_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3741l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3741l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3741l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3741l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3755_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3741l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3755 :
    hubcapFit theRedpart rf8 p8_3741l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3755_1, c8_3755_2, c8_3755_3, c8_3755_4, c8_3755_5, c8_3755_6, c8_3755_7, c8_3755_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3740l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3740l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3740l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3740l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3757_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3740l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3757 :
    hubcapFit theRedpart rf8 p8_3740l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3757_1, c8_3757_2, c8_3757_3, c8_3757_4, c8_3757_5, c8_3757_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3737l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3737l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3737l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3737l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3737l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3759_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3737l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3759 :
    hubcapFit theRedpart rf8 p8_3737l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3759_1, c8_3759_2, c8_3759_3, c8_3759_4, c8_3759_5, c8_3759_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3736l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3736l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3761_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3736l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3761 :
    hubcapFit theRedpart rf8 p8_3736l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3761_1, c8_3761_2, c8_3761_3, c8_3761_4, c8_3761_5, c8_3761_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3735l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3735l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3762_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3735l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3762 :
    hubcapFit theRedpart rf8 p8_3735l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3762_1, c8_3762_2, c8_3762_3, c8_3762_4, c8_3762_5, c8_3762_6, c8_3762_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3734l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3734l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3734l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3734l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3764_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3734l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3764 :
    hubcapFit theRedpart rf8 p8_3734l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3764_1, c8_3764_2, c8_3764_3, c8_3764_4, c8_3764_5, c8_3764_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3713l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3713l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3766_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3713l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3766 :
    hubcapFit theRedpart rf8 p8_3713l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3766_1, c8_3766_2, c8_3766_3, c8_3766_4, c8_3766_5, c8_3766_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3712l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3712l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3712l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3767_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3712l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3767 :
    hubcapFit theRedpart rf8 p8_3712l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3767_1, c8_3767_2, c8_3767_3, c8_3767_4, c8_3767_5, c8_3767_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3631l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3631l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3769_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3631l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3769 :
    hubcapFit theRedpart rf8 p8_3631l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3769_1, c8_3769_2, c8_3769_3, c8_3769_4, c8_3769_5, c8_3769_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3786r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3786r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3786r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3786r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3786r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3786r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3786r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3787_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3786r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3787 :
    hubcapFit theRedpart rf8 p8_3786r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3787_1, c8_3787_2, c8_3787_3, c8_3787_4, c8_3787_5, c8_3787_6, c8_3787_7, c8_3787_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3786l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3786l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3788_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3786l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3788 :
    hubcapFit theRedpart rf8 p8_3786l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3788_1, c8_3788_2, c8_3788_3, c8_3788_4, c8_3788_5, c8_3788_6, c8_3788_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3784l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3784l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3784l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3784l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3784l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3790_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3784l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3790 :
    hubcapFit theRedpart rf8 p8_3784l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3790_1, c8_3790_2, c8_3790_3, c8_3790_4, c8_3790_5, c8_3790_6, c8_3790_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3783l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3783l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3783l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3783l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3783l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3783l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3792_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3783l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3792 :
    hubcapFit theRedpart rf8 p8_3783l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3792_1, c8_3792_2, c8_3792_3, c8_3792_4, c8_3792_5, c8_3792_6, c8_3792_7]

end FourColor

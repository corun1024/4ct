import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 69 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3735r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3735r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3735r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3735r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3736_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3735r) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3736 :
    hubcapFit theRedpart rf7 p7_3735r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3736_1, c7_3736_2, c7_3736_3, c7_3736_4, c7_3736_5, c7_3736_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3735l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3737_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3735l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3737 :
    hubcapFit theRedpart rf7 p7_3735l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3737_1, c7_3737_2, c7_3737_3, c7_3737_4, c7_3737_5, c7_3737_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3734l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3739_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3734l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3739 :
    hubcapFit theRedpart rf7 p7_3734l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3739_1, c7_3739_2, c7_3739_3, c7_3739_4, c7_3739_5, c7_3739_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3733l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3733l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3733l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3733l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3740_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3733l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3740 :
    hubcapFit theRedpart rf7 p7_3733l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3740_1, c7_3740_2, c7_3740_3, c7_3740_4, c7_3740_5, c7_3740_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3732l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3732l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3732l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3732l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3732l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3742_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3732l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3742 :
    hubcapFit theRedpart rf7 p7_3732l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3742_1, c7_3742_2, c7_3742_3, c7_3742_4, c7_3742_5, c7_3742_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3731l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3731l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3731l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3731l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3731l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3743_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3731l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3743 :
    hubcapFit theRedpart rf7 p7_3731l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3743_1, c7_3743_2, c7_3743_3, c7_3743_4, c7_3743_5, c7_3743_6, c7_3743_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3730l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3730l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3745_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3730l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3745 :
    hubcapFit theRedpart rf7 p7_3730l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3745_1, c7_3745_2, c7_3745_3, c7_3745_4, c7_3745_5, c7_3745_6, c7_3745_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3747_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3747_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3728l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3747_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3728l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3747_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3728l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3747_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3728l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3747 :
    hubcapFit theRedpart rf7 p7_3728l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3747_1, c7_3747_2, c7_3747_3, c7_3747_4, c7_3747_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3727l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3727l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3727l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3727l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3727l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3749_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3727l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3749 :
    hubcapFit theRedpart rf7 p7_3727l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3749_1, c7_3749_2, c7_3749_3, c7_3749_4, c7_3749_5, c7_3749_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3726l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3726l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3726l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3726l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3726l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3750_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3726l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3750 :
    hubcapFit theRedpart rf7 p7_3726l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3750_1, c7_3750_2, c7_3750_3, c7_3750_4, c7_3750_5, c7_3750_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3725l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3725l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3725l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3725l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3725l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3752_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3725l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3752 :
    hubcapFit theRedpart rf7 p7_3725l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3752_1, c7_3752_2, c7_3752_3, c7_3752_4, c7_3752_5, c7_3752_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3704l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3704l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3704l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3704l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3754_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3704l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3754 :
    hubcapFit theRedpart rf7 p7_3704l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3754_1, c7_3754_2, c7_3754_3, c7_3754_4, c7_3754_5, c7_3754_6, c7_3754_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3768r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3768r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3768r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3768r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3768r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3769_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3768r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3769 :
    hubcapFit theRedpart rf7 p7_3768r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3769_1, c7_3769_2, c7_3769_3, c7_3769_4, c7_3769_5, c7_3769_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3768l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3768l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3768l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3770_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3768l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3770 :
    hubcapFit theRedpart rf7 p7_3768l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3770_1, c7_3770_2, c7_3770_3, c7_3770_4, c7_3770_5, c7_3770_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3772_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3772_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3772_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3766l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3772_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3766l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3772_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3766l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3772 :
    hubcapFit theRedpart rf7 p7_3766l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3772_1, c7_3772_2, c7_3772_3, c7_3772_4, c7_3772_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3765l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3765l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3765l) (hubSubn 7 4 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3765l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3765l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3774_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3765l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3774 :
    hubcapFit theRedpart rf7 p7_3765l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 0 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3774_1, c7_3774_2, c7_3774_3, c7_3774_4, c7_3774_5, c7_3774_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3764l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3764l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3764l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3764l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3775_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3764l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3775 :
    hubcapFit theRedpart rf7 p7_3764l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3775_1, c7_3775_2, c7_3775_3, c7_3775_4, c7_3775_5, c7_3775_6]

end FourColor

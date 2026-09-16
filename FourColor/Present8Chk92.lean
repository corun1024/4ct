import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 92 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4593l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4598_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4593l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4598 :
    hubcapFit theRedpart rf8 p8_4593l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4598_1, c8_4598_2, c8_4598_3, c8_4598_4, c8_4598_5, c8_4598_6, c8_4598_7, c8_4598_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4592l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4600_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4600 :
    hubcapFit theRedpart rf8 p8_4592l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4600_1, c8_4600_2, c8_4600_3, c8_4600_4, c8_4600_5, c8_4600_6, c8_4600_7, c8_4600_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4603_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4602l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4603_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4602l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4603_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4602l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4603_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4602l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4603_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4602l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4603 :
    hubcapFit theRedpart rf8 p8_4602l
    (Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4603_1, c8_4603_2, c8_4603_3, c8_4603_4, c8_4603_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4605_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4602r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4605_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4602r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4605_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4602r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4605_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4602r) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4605_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4602r) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4605 :
    hubcapFit theRedpart rf8 p8_4602r
    (Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4605_1, c8_4605_2, c8_4605_3, c8_4605_4, c8_4605_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4608l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4608l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4608l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4609_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4608l) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4609 :
    hubcapFit theRedpart rf8 p8_4608l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4609_1, c8_4609_2, c8_4609_3, c8_4609_4, c8_4609_5, c8_4609_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4608r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4608r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4608r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4608r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4608r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4611_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4608r) (hubSubn 8 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4611 :
    hubcapFit theRedpart rf8 p8_4608r
    (Hubcap.one 1 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4611_1, c8_4611_2, c8_4611_3, c8_4611_4, c8_4611_5, c8_4611_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4513l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4513l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4513l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4513l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4513l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4614_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4513l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4614 :
    hubcapFit theRedpart rf8 p8_4513l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4614_1, c8_4614_2, c8_4614_3, c8_4614_4, c8_4614_5, c8_4614_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4625r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4625r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4625r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4625r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4625r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4625r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4626_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4625r) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4626 :
    hubcapFit theRedpart rf8 p8_4625r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4626_1, c8_4626_2, c8_4626_3, c8_4626_4, c8_4626_5, c8_4626_6, c8_4626_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4627_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4625l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4627 :
    hubcapFit theRedpart rf8 p8_4625l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4627_1, c8_4627_2, c8_4627_3, c8_4627_4, c8_4627_5, c8_4627_6, c8_4627_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4624l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4629_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4624l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4629 :
    hubcapFit theRedpart rf8 p8_4624l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4629_1, c8_4629_2, c8_4629_3, c8_4629_4, c8_4629_5, c8_4629_6, c8_4629_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4623l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4623l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4623l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4631_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4623l) (hubSubn 8 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4631 :
    hubcapFit theRedpart rf8 p8_4623l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4631_1, c8_4631_2, c8_4631_3, c8_4631_4, c8_4631_5, c8_4631_6, c8_4631_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4622l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4622l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4622l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4622l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4622l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4622l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4633_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4622l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4633 :
    hubcapFit theRedpart rf8 p8_4622l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4633_1, c8_4633_2, c8_4633_3, c8_4633_4, c8_4633_5, c8_4633_6, c8_4633_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4621l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4621l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4621l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4635_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4621l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4635 :
    hubcapFit theRedpart rf8 p8_4621l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4635_1, c8_4635_2, c8_4635_3, c8_4635_4, c8_4635_5, c8_4635_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4620l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4620l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4636_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4620l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4636 :
    hubcapFit theRedpart rf8 p8_4620l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4636_1, c8_4636_2, c8_4636_3, c8_4636_4, c8_4636_5, c8_4636_6, c8_4636_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4619l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4619l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4619l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4638_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4619l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4638 :
    hubcapFit theRedpart rf8 p8_4619l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4638_1, c8_4638_2, c8_4638_3, c8_4638_4, c8_4638_5, c8_4638_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4618l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4618l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4639_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4618l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4639 :
    hubcapFit theRedpart rf8 p8_4618l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4639_1, c8_4639_2, c8_4639_3, c8_4639_4, c8_4639_5, c8_4639_6]

end FourColor

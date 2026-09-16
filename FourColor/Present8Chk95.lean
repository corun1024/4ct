import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 95 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4743l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4748_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4743l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4748 :
    hubcapFit theRedpart rf8 p8_4743l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4748_1, c8_4748_2, c8_4748_3, c8_4748_4, c8_4748_5, c8_4748_6, c8_4748_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4742l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4742l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4750_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4742l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4750 :
    hubcapFit theRedpart rf8 p8_4742l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4750_1, c8_4750_2, c8_4750_3, c8_4750_4, c8_4750_5, c8_4750_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4741l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4741l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4751_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4741l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4751 :
    hubcapFit theRedpart rf8 p8_4741l
    (Hubcap.one 2 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4751_1, c8_4751_2, c8_4751_3, c8_4751_4, c8_4751_5, c8_4751_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4718l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4718l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4718l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4718l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4718l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4753_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4718l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4753 :
    hubcapFit theRedpart rf8 p8_4718l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4753_1, c8_4753_2, c8_4753_3, c8_4753_4, c8_4753_5, c8_4753_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4717l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4717l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4717l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4717l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4755_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4717l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4755 :
    hubcapFit theRedpart rf8 p8_4717l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4755_1, c8_4755_2, c8_4755_3, c8_4755_4, c8_4755_5, c8_4755_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4716l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4716l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4716l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4756_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4716l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4756 :
    hubcapFit theRedpart rf8 p8_4716l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4756_1, c8_4756_2, c8_4756_3, c8_4756_4, c8_4756_5, c8_4756_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4715l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4715l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4715l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4758_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4715l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4758 :
    hubcapFit theRedpart rf8 p8_4715l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4758_1, c8_4758_2, c8_4758_3, c8_4758_4, c8_4758_5, c8_4758_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4766r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4766r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4766r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4766r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4766r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4766r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4766r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4767_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4766r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4767 :
    hubcapFit theRedpart rf8 p8_4766r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4767_1, c8_4767_2, c8_4767_3, c8_4767_4, c8_4767_5, c8_4767_6, c8_4767_7, c8_4767_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4777r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4777r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4777r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4778_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4777r) (hubSubn 8 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4778 :
    hubcapFit theRedpart rf8 p8_4777r
    (Hubcap.one 0 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4778_1, c8_4778_2, c8_4778_3, c8_4778_4, c8_4778_5, c8_4778_6, c8_4778_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4774l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4774l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4774l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4780_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4774l) (hubSubn 8 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4780 :
    hubcapFit theRedpart rf8 p8_4774l
    (Hubcap.one 0 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4780_1, c8_4780_2, c8_4780_3, c8_4780_4, c8_4780_5, c8_4780_6, c8_4780_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4773l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4773l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4773l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4782_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4773l) (hubSubn 8 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4782 :
    hubcapFit theRedpart rf8 p8_4773l
    (Hubcap.one 0 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4782_1, c8_4782_2, c8_4782_3, c8_4782_4, c8_4782_5, c8_4782_6, c8_4782_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4785r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4785r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4785r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4785r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4785r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4785r) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4785r) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4786_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4785r) (hubSubn 8 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4786 :
    hubcapFit theRedpart rf8 p8_4785r
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4786_1, c8_4786_2, c8_4786_3, c8_4786_4, c8_4786_5, c8_4786_6, c8_4786_7, c8_4786_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4785l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4785l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4787_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4785l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4787 :
    hubcapFit theRedpart rf8 p8_4785l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4787_1, c8_4787_2, c8_4787_3, c8_4787_4, c8_4787_5, c8_4787_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4784l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4784l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4784l) (hubSubn 8 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4789_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4784l) (hubSubn 8 4 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4789 :
    hubcapFit theRedpart rf8 p8_4784l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4789_1, c8_4789_2, c8_4789_3, c8_4789_4, c8_4789_5, c8_4789_6, c8_4789_7, c8_4789_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4770l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4770l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4770l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4770l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4791_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4770l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4791 :
    hubcapFit theRedpart rf8 p8_4770l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4791_1, c8_4791_2, c8_4791_3, c8_4791_4, c8_4791_5, c8_4791_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4795r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4795r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4795r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4795r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4795r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4795r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4795r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4796_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4795r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4796 :
    hubcapFit theRedpart rf8 p8_4795r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4796_1, c8_4796_2, c8_4796_3, c8_4796_4, c8_4796_5, c8_4796_6, c8_4796_7, c8_4796_8]

end FourColor

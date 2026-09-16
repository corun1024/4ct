import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 88 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4390l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4390l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4390l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4390l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4390l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4401_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4390l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4401 :
    hubcapFit theRedpart rf8 p8_4390l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4401_1, c8_4401_2, c8_4401_3, c8_4401_4, c8_4401_5, c8_4401_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4389l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4389l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4389l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4402_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4389l) (hubSubn 8 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4402 :
    hubcapFit theRedpart rf8 p8_4389l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4402_1, c8_4402_2, c8_4402_3, c8_4402_4, c8_4402_5, c8_4402_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4388l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4388l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4388l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4404_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4388l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4404 :
    hubcapFit theRedpart rf8 p8_4388l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4404_1, c8_4404_2, c8_4404_3, c8_4404_4, c8_4404_5, c8_4404_6, c8_4404_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4387l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4387l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4406_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4387l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4406 :
    hubcapFit theRedpart rf8 p8_4387l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4406_1, c8_4406_2, c8_4406_3, c8_4406_4, c8_4406_5, c8_4406_6, c8_4406_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4369l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4369l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4369l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4369l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4369l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4369l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4409_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4369l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4409 :
    hubcapFit theRedpart rf8 p8_4369l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4409_1, c8_4409_2, c8_4409_3, c8_4409_4, c8_4409_5, c8_4409_6, c8_4409_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4418r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4418r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4418r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4418r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4418r) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4419_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4418r) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4419 :
    hubcapFit theRedpart rf8 p8_4418r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4419_1, c8_4419_2, c8_4419_3, c8_4419_4, c8_4419_5, c8_4419_6, c8_4419_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4420_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4418l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4420_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4418l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4420_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4418l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4420_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4418l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4420_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4418l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4420 :
    hubcapFit theRedpart rf8 p8_4418l
    (Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4420_1, c8_4420_2, c8_4420_3, c8_4420_4, c8_4420_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4417l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4422_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4417l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4422 :
    hubcapFit theRedpart rf8 p8_4417l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4422_1, c8_4422_2, c8_4422_3, c8_4422_4, c8_4422_5, c8_4422_6, c8_4422_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4416l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4416l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4416l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4416l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4424_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4416l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4424 :
    hubcapFit theRedpart rf8 p8_4416l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4424_1, c8_4424_2, c8_4424_3, c8_4424_4, c8_4424_5, c8_4424_6, c8_4424_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4432r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4432r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4432r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4432r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4432r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4433_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4432r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4433 :
    hubcapFit theRedpart rf8 p8_4432r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4433_1, c8_4433_2, c8_4433_3, c8_4433_4, c8_4433_5, c8_4433_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4432l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4432l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4432l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4432l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4432l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4434_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4432l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4434 :
    hubcapFit theRedpart rf8 p8_4432l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4434_1, c8_4434_2, c8_4434_3, c8_4434_4, c8_4434_5, c8_4434_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4430l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4430l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4430l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4430l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4430l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4430l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4436_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4430l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4436 :
    hubcapFit theRedpart rf8 p8_4430l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4436_1, c8_4436_2, c8_4436_3, c8_4436_4, c8_4436_5, c8_4436_6, c8_4436_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4429l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4429l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4429l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4438_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4429l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4438 :
    hubcapFit theRedpart rf8 p8_4429l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4438_1, c8_4438_2, c8_4438_3, c8_4438_4, c8_4438_5, c8_4438_6, c8_4438_7, c8_4438_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4440_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4428l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4440_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4428l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4440_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4428l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4440_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4428l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4440_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4428l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4440 :
    hubcapFit theRedpart rf8 p8_4428l
    (Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4440_1, c8_4440_2, c8_4440_3, c8_4440_4, c8_4440_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4441_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4427l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4441_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4427l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4441_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4427l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4441_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4427l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4441_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4427l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4441 :
    hubcapFit theRedpart rf8 p8_4427l
    (Hubcap.one 0 4 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4441_1, c8_4441_2, c8_4441_3, c8_4441_4, c8_4441_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4443_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4426l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4443_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4426l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4443_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4426l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4443_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4426l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4443_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4426l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4443 :
    hubcapFit theRedpart rf8 p8_4426l
    (Hubcap.one 0 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4443_1, c8_4443_2, c8_4443_3, c8_4443_4, c8_4443_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4412l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4412l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4412l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4412l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4412l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4445_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4412l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4445 :
    hubcapFit theRedpart rf8 p8_4412l
    (Hubcap.one 6 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4445_1, c8_4445_2, c8_4445_3, c8_4445_4, c8_4445_5, c8_4445_6]

end FourColor

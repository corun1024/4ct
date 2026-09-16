import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 70 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3763l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3763l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3763l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3763l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3763l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3763l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3777_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3763l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3777 :
    hubcapFit theRedpart rf7 p7_3763l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 5 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3777_1, c7_3777_2, c7_3777_3, c7_3777_4, c7_3777_5, c7_3777_6, c7_3777_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3779_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3779_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3779_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3779_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3762l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3779_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3762l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3779 :
    hubcapFit theRedpart rf7 p7_3762l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3779_1, c7_3779_2, c7_3779_3, c7_3779_4, c7_3779_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3780_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3761l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3780_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3761l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3780_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3761l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3780_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3761l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3780_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3761l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3780 :
    hubcapFit theRedpart rf7 p7_3761l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3780_1, c7_3780_2, c7_3780_3, c7_3780_4, c7_3780_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3782_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3760l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3782_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3760l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3782_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3760l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3782_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3760l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3782_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3760l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3782 :
    hubcapFit theRedpart rf7 p7_3760l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3782_1, c7_3782_2, c7_3782_3, c7_3782_4, c7_3782_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3759l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3759l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3759l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3759l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3759l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3783_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3759l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3783 :
    hubcapFit theRedpart rf7 p7_3759l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3783_1, c7_3783_2, c7_3783_3, c7_3783_4, c7_3783_5, c7_3783_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3793r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3793r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3793r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3793r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3793r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3794_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3793r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3794 :
    hubcapFit theRedpart rf7 p7_3793r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3794_1, c7_3794_2, c7_3794_3, c7_3794_4, c7_3794_5, c7_3794_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3795_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3793l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3795_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3793l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3795_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3793l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3795_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3793l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3795_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3793l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3795 :
    hubcapFit theRedpart rf7 p7_3793l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3795_1, c7_3795_2, c7_3795_3, c7_3795_4, c7_3795_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3797_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3791l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3797_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3791l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3797_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3791l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3797_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3791l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3797_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3791l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3797 :
    hubcapFit theRedpart rf7 p7_3791l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3797_1, c7_3797_2, c7_3797_3, c7_3797_4, c7_3797_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3799_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3790l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3799_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3790l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3799_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3790l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3799_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3790l) (hubSubn 7 3 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3799_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3790l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3799 :
    hubcapFit theRedpart rf7 p7_3790l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 1 3 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3799_1, c7_3799_2, c7_3799_3, c7_3799_4, c7_3799_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3789l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3789l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3789l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3789l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3789l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3800_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3789l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3800 :
    hubcapFit theRedpart rf7 p7_3789l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3800_1, c7_3800_2, c7_3800_3, c7_3800_4, c7_3800_5, c7_3800_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3802_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3786l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3802_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3786l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3802_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3786l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3802_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3786l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3802_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3786l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3802 :
    hubcapFit theRedpart rf7 p7_3786l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 (-1) <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3802_1, c7_3802_2, c7_3802_3, c7_3802_4, c7_3802_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3826r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3826r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3826r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3826r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3827_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3826r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3827 :
    hubcapFit theRedpart rf7 p7_3826r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3827_1, c7_3827_2, c7_3827_3, c7_3827_4, c7_3827_5, c7_3827_6, c7_3827_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3826l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3826l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3826l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3826l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3828_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3828 :
    hubcapFit theRedpart rf7 p7_3826l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3828_1, c7_3828_2, c7_3828_3, c7_3828_4, c7_3828_5, c7_3828_6, c7_3828_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3825l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3825l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3825l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3830_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3825l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3830 :
    hubcapFit theRedpart rf7 p7_3825l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3830_1, c7_3830_2, c7_3830_3, c7_3830_4, c7_3830_5, c7_3830_6, c7_3830_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3823l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3823l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3823l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3823l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3832_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3823l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3832 :
    hubcapFit theRedpart rf7 p7_3823l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3832_1, c7_3832_2, c7_3832_3, c7_3832_4, c7_3832_5, c7_3832_6, c7_3832_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3822l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3822l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3822l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3834_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3822l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3834 :
    hubcapFit theRedpart rf7 p7_3822l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3834_1, c7_3834_2, c7_3834_3, c7_3834_4, c7_3834_5, c7_3834_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3821l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3821l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3835_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3821l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3835 :
    hubcapFit theRedpart rf7 p7_3821l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3835_1, c7_3835_2, c7_3835_3, c7_3835_4, c7_3835_5, c7_3835_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3820l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3820l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_3837_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_3820l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_3837 :
    hubcapFit theRedpart rf7 p7_3820l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_3837_1, c7_3837_2, c7_3837_3, c7_3837_4, c7_3837_5, c7_3837_6]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 96 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4795l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4795l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4795l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4795l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4797_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4795l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4797 :
    hubcapFit theRedpart rf8 p8_4795l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4797_1, c8_4797_2, c8_4797_3, c8_4797_4, c8_4797_5, c8_4797_6, c8_4797_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4794l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4794l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4799_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4794l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4799 :
    hubcapFit theRedpart rf8 p8_4794l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4799_1, c8_4799_2, c8_4799_3, c8_4799_4, c8_4799_5, c8_4799_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4819r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4819r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4819r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4819r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4819r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4819r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4820_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4819r) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4820 :
    hubcapFit theRedpart rf8 p8_4819r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4820_1, c8_4820_2, c8_4820_3, c8_4820_4, c8_4820_5, c8_4820_6, c8_4820_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4819l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4819l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4821_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4819l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4821 :
    hubcapFit theRedpart rf8 p8_4819l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4821_1, c8_4821_2, c8_4821_3, c8_4821_4, c8_4821_5, c8_4821_6, c8_4821_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4818l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4818l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4818l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4818l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4818l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4818l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4823_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4818l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4823 :
    hubcapFit theRedpart rf8 p8_4818l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4823_1, c8_4823_2, c8_4823_3, c8_4823_4, c8_4823_5, c8_4823_6, c8_4823_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4826r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4826r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4826r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4826r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4826r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4826r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4827_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4826r) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4827 :
    hubcapFit theRedpart rf8 p8_4826r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4827_1, c8_4827_2, c8_4827_3, c8_4827_4, c8_4827_5, c8_4827_6, c8_4827_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4826l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4826l) (hubSubn 8 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4826l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4828_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4826l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4828 :
    hubcapFit theRedpart rf8 p8_4826l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4828_1, c8_4828_2, c8_4828_3, c8_4828_4, c8_4828_5, c8_4828_6, c8_4828_7, c8_4828_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4825l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4825l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4825l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4825l) (hubSubn 8 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4830_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4825l) (hubSubn 8 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4830 :
    hubcapFit theRedpart rf8 p8_4825l
    (Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4830_1, c8_4830_2, c8_4830_3, c8_4830_4, c8_4830_5, c8_4830_6, c8_4830_7, c8_4830_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4834r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4834r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4834r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4834r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4834r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4834r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4835_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4834r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4835 :
    hubcapFit theRedpart rf8 p8_4834r
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4835_1, c8_4835_2, c8_4835_3, c8_4835_4, c8_4835_5, c8_4835_6, c8_4835_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4834l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4834l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4834l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4834l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4836_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4834l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4836 :
    hubcapFit theRedpart rf8 p8_4834l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4836_1, c8_4836_2, c8_4836_3, c8_4836_4, c8_4836_5, c8_4836_6, c8_4836_7, c8_4836_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4833l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4833l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4833l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4833l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4833l) (hubSubn 8 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4838_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4833l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4838 :
    hubcapFit theRedpart rf8 p8_4833l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4838_1, c8_4838_2, c8_4838_3, c8_4838_4, c8_4838_5, c8_4838_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4841r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4841r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4842_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4841r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4842 :
    hubcapFit theRedpart rf8 p8_4841r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4842_1, c8_4842_2, c8_4842_3, c8_4842_4, c8_4842_5, c8_4842_6, c8_4842_7, c8_4842_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4841l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4843_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4843 :
    hubcapFit theRedpart rf8 p8_4841l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4843_1, c8_4843_2, c8_4843_3, c8_4843_4, c8_4843_5, c8_4843_6, c8_4843_7, c8_4843_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4840l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4840l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4840l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4840l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4840l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4840l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4845_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4840l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4845 :
    hubcapFit theRedpart rf8 p8_4840l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4845_1, c8_4845_2, c8_4845_3, c8_4845_4, c8_4845_5, c8_4845_6, c8_4845_7, c8_4845_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4839l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4847_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4847 :
    hubcapFit theRedpart rf8 p8_4839l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4847_1, c8_4847_2, c8_4847_3, c8_4847_4, c8_4847_5, c8_4847_6, c8_4847_7, c8_4847_8]

end FourColor

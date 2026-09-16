import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 16 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_802l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_802l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_802l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_802l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_802l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_803_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_802l) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_803 :
    hubcapFit theRedpart rf8 p8_802l
    (Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_803_1, c8_803_2, c8_803_3, c8_803_4, c8_803_5, c8_803_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_802r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_802r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_802r) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_802r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_802r) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_805_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_802r) (hubSubn 8 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_805 :
    hubcapFit theRedpart rf8 p8_802r
    (Hubcap.one 6 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_805_1, c8_805_2, c8_805_3, c8_805_4, c8_805_5, c8_805_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_809r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_809r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_809r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_809r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_809r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_810_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_809r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_810 :
    hubcapFit theRedpart rf8 p8_809r
    (Hubcap.one 2 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_810_1, c8_810_2, c8_810_3, c8_810_4, c8_810_5, c8_810_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_809l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_809l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_809l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_809l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_809l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_811_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_809l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_811 :
    hubcapFit theRedpart rf8 p8_809l
    (Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_811_1, c8_811_2, c8_811_3, c8_811_4, c8_811_5, c8_811_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_808l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_808l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_808l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_808l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_813_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_808l) (hubSubn 8 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_813 :
    hubcapFit theRedpart rf8 p8_808l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_813_1, c8_813_2, c8_813_3, c8_813_4, c8_813_5, c8_813_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_829r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_829r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_829r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_829r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_830_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_829r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_830 :
    hubcapFit theRedpart rf8 p8_829r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_830_1, c8_830_2, c8_830_3, c8_830_4, c8_830_5, c8_830_6, c8_830_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_829l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_831_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_829l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_831 :
    hubcapFit theRedpart rf8 p8_829l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_831_1, c8_831_2, c8_831_3, c8_831_4, c8_831_5, c8_831_6, c8_831_7, c8_831_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_826l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_826l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_826l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_833_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_826l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_833 :
    hubcapFit theRedpart rf8 p8_826l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_833_1, c8_833_2, c8_833_3, c8_833_4, c8_833_5, c8_833_6, c8_833_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_846r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_846r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_846r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_846r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_846r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_846r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_847_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_846r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_847 :
    hubcapFit theRedpart rf8 p8_846r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_847_1, c8_847_2, c8_847_3, c8_847_4, c8_847_5, c8_847_6, c8_847_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_846l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_846l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_848_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_846l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_848 :
    hubcapFit theRedpart rf8 p8_846l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_848_1, c8_848_2, c8_848_3, c8_848_4, c8_848_5, c8_848_6, c8_848_7, c8_848_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_850_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_845l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_850 :
    hubcapFit theRedpart rf8 p8_845l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_850_1, c8_850_2, c8_850_3, c8_850_4, c8_850_5, c8_850_6, c8_850_7, c8_850_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_844l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_844l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_844l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_844l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_844l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_844l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_852_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_844l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_852 :
    hubcapFit theRedpart rf8 p8_844l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_852_1, c8_852_2, c8_852_3, c8_852_4, c8_852_5, c8_852_6, c8_852_7, c8_852_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_843l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_843l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_843l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_843l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_854_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_854 :
    hubcapFit theRedpart rf8 p8_843l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_854_1, c8_854_2, c8_854_3, c8_854_4, c8_854_5, c8_854_6, c8_854_7, c8_854_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_842l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_856_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_842l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_856 :
    hubcapFit theRedpart rf8 p8_842l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_856_1, c8_856_2, c8_856_3, c8_856_4, c8_856_5, c8_856_6, c8_856_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_838l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_838l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_838l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_858_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_838l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_858 :
    hubcapFit theRedpart rf8 p8_838l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_858_1, c8_858_2, c8_858_3, c8_858_4, c8_858_5, c8_858_6, c8_858_7, c8_858_8]

end FourColor

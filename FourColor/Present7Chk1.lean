import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_22_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_21r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_22_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_21r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_22_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_21r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_22_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_21r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_22_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_21r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_22 :
    hubcapFit theRedpart rf7 p7_21r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_22_1, c7_22_2, c7_22_3, c7_22_4, c7_22_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_29_1 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_28r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_29_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_28r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_29_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_28r) (hubSubn 7 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_29_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_28r) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_29_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_28r) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_29 :
    hubcapFit theRedpart rf7 p7_28r
    (Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_29_1, c7_29_2, c7_29_3, c7_29_4, c7_29_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_28l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_28l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_28l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_28l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_28l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_30_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_28l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_30 :
    hubcapFit theRedpart rf7 p7_28l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_30_1, c7_30_2, c7_30_3, c7_30_4, c7_30_5, c7_30_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_32_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_27l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_32_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_27l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_32_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_27l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_32_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_27l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_32 :
    hubcapFit theRedpart rf7 p7_27l
    (Hubcap.one 2 1 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_32_1, c7_32_2, c7_32_3, c7_32_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_57_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_56r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_57_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_56r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_57_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_56r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_57_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_56r) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_57_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_56r) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_57 :
    hubcapFit theRedpart rf7 p7_56r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_57_1, c7_57_2, c7_57_3, c7_57_4, c7_57_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_58_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_56l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_58_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_56l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_58_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_56l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_58_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_56l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_58 :
    hubcapFit theRedpart rf7 p7_56l
    (Hubcap.one 1 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_58_1, c7_58_2, c7_58_3, c7_58_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_60_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_55l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_60_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_55l) (hubSubn 7 1 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_60_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_55l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_60_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_55l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_60 :
    hubcapFit theRedpart rf7 p7_55l
    (Hubcap.one 4 2 <|
     Hubcap.two 0 1 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_60_1, c7_60_2, c7_60_3, c7_60_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_61_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_54l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_61_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_54l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_61_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_54l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_61_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_54l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_61_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_54l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_61 :
    hubcapFit theRedpart rf7 p7_54l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_61_1, c7_61_2, c7_61_3, c7_61_4, c7_61_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_63_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_53l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_63_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_53l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_63_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_53l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_63_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_53l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_63 :
    hubcapFit theRedpart rf7 p7_53l
    (Hubcap.one 1 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_63_1, c7_63_2, c7_63_3, c7_63_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_64_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_52l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_64_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_52l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_64_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_52l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_64_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_52l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_64_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_52l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_64 :
    hubcapFit theRedpart rf7 p7_52l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_64_1, c7_64_2, c7_64_3, c7_64_4, c7_64_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_66_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_51l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_66_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_51l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_66_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_51l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_66_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_51l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_66_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_51l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_66 :
    hubcapFit theRedpart rf7 p7_51l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_66_1, c7_66_2, c7_66_3, c7_66_4, c7_66_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_67_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_50l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_67_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_50l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_67_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_50l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_67_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_50l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_67_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_50l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_67 :
    hubcapFit theRedpart rf7 p7_50l
    (Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_67_1, c7_67_2, c7_67_3, c7_67_4, c7_67_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_70_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_69r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_70_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_69r) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_70_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_69r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_70_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_69r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_70 :
    hubcapFit theRedpart rf7 p7_69r
    (Hubcap.one 6 1 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_70_1, c7_70_2, c7_70_3, c7_70_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_71_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_69l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_71_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_69l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_71_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_69l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_71_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_69l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_71 :
    hubcapFit theRedpart rf7 p7_69l
    (Hubcap.one 1 1 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_71_1, c7_71_2, c7_71_3, c7_71_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_73_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_47l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_73_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_47l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_73_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_47l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_73_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_47l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_73 :
    hubcapFit theRedpart rf7 p7_47l
    (Hubcap.one 6 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_73_1, c7_73_2, c7_73_3, c7_73_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_75_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_46l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_75_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_46l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_75_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_46l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_75_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_46l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_75 :
    hubcapFit theRedpart rf7 p7_46l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_75_1, c7_75_2, c7_75_3, c7_75_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_76_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_45l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_76_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_45l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_76_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_45l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_76_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_45l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_76 :
    hubcapFit theRedpart rf7 p7_45l
    (Hubcap.one 6 2 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_76_1, c7_76_2, c7_76_3, c7_76_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_78_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_44l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_78_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_44l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_78_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_44l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_78_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_44l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_78 :
    hubcapFit theRedpart rf7 p7_44l
    (Hubcap.one 1 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_78_1, c7_78_2, c7_78_3, c7_78_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_79_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_43l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_79_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_43l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_79_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_43l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_79_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_43l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_79_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_43l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_79 :
    hubcapFit theRedpart rf7 p7_43l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_79_1, c7_79_2, c7_79_3, c7_79_4, c7_79_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_96_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_95r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_96_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_95r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_96_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_95r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_96_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_95r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_96 :
    hubcapFit theRedpart rf7 p7_95r
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_96_1, c7_96_2, c7_96_3, c7_96_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_97_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_95l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_97_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_95l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_97_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_95l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_97_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_95l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_97 :
    hubcapFit theRedpart rf7 p7_95l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_97_1, c7_97_2, c7_97_3, c7_97_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_104_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_103r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_104_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_103r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_104_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_103r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_104_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_103r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_104_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_103r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_104 :
    hubcapFit theRedpart rf7 p7_103r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_104_1, c7_104_2, c7_104_3, c7_104_4, c7_104_5]

end FourColor

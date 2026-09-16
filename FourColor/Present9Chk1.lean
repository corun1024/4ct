import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_9r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_9r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_9r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_9r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_9r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_10_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_9r) (hubSubn 9 8 7) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_10 :
    hubcapFit theRedpart rf9 p9_9r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 7 8 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_10_1, c9_10_2, c9_10_3, c9_10_4, c9_10_5, c9_10_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_21r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_21r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_21r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_21r) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_21r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_22_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_21r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_22 :
    hubcapFit theRedpart rf9 p9_21r
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_22_1, c9_22_2, c9_22_3, c9_22_4, c9_22_5, c9_22_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_49r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_49r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_49r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_49r) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_49r) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_50_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_49r) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_50 :
    hubcapFit theRedpart rf9 p9_49r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_50_1, c9_50_2, c9_50_3, c9_50_4, c9_50_5, c9_50_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_49l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_49l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_49l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_49l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_49l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_51_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_49l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_51 :
    hubcapFit theRedpart rf9 p9_49l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_51_1, c9_51_2, c9_51_3, c9_51_4, c9_51_5, c9_51_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_46l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_46l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_46l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_53_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_46l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_53 :
    hubcapFit theRedpart rf9 p9_46l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_53_1, c9_53_2, c9_53_3, c9_53_4, c9_53_5, c9_53_6, c9_53_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_44l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_44l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_44l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_44l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_44l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_44l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_55_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_44l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_55 :
    hubcapFit theRedpart rf9 p9_44l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_55_1, c9_55_2, c9_55_3, c9_55_4, c9_55_5, c9_55_6, c9_55_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_42l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_42l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_42l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_42l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_57_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_42l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_57 :
    hubcapFit theRedpart rf9 p9_42l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_57_1, c9_57_2, c9_57_3, c9_57_4, c9_57_5, c9_57_6, c9_57_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_40l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_40l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_40l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_40l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_40l) (hubSubn 9 8 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_59_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_40l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_59 :
    hubcapFit theRedpart rf9 p9_40l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 5 8 5 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_59_1, c9_59_2, c9_59_3, c9_59_4, c9_59_5, c9_59_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_39l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_39l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_39l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_39l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_39l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_39l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_39l) (hubSubn 9 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_61_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_39l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_61 :
    hubcapFit theRedpart rf9 p9_39l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 4 6 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_61_1, c9_61_2, c9_61_3, c9_61_4, c9_61_5, c9_61_6, c9_61_7, c9_61_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_38l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_38l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_38l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_38l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_38l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_38l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_63_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_38l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_63 :
    hubcapFit theRedpart rf9 p9_38l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_63_1, c9_63_2, c9_63_3, c9_63_4, c9_63_5, c9_63_6, c9_63_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_36l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_36l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_36l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_36l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_36l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_36l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_65_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_36l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_65 :
    hubcapFit theRedpart rf9 p9_36l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_65_1, c9_65_2, c9_65_3, c9_65_4, c9_65_5, c9_65_6, c9_65_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_34l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_34l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_34l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_34l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_34l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_67_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_34l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_67 :
    hubcapFit theRedpart rf9 p9_34l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_67_1, c9_67_2, c9_67_3, c9_67_4, c9_67_5, c9_67_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_33l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_33l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_69_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_33l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_69 :
    hubcapFit theRedpart rf9 p9_33l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_69_1, c9_69_2, c9_69_3, c9_69_4, c9_69_5, c9_69_6, c9_69_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_32l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_32l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_71_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_32l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_71 :
    hubcapFit theRedpart rf9 p9_32l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_71_1, c9_71_2, c9_71_3, c9_71_4, c9_71_5, c9_71_6, c9_71_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_31l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_31l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_31l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_31l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_31l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_73_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_31l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_73 :
    hubcapFit theRedpart rf9 p9_31l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_73_1, c9_73_2, c9_73_3, c9_73_4, c9_73_5, c9_73_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_30l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_30l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_30l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_30l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_30l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_74_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_30l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_74 :
    hubcapFit theRedpart rf9 p9_30l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_74_1, c9_74_2, c9_74_3, c9_74_4, c9_74_5, c9_74_6]

end FourColor

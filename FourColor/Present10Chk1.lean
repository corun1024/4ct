import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_27r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_27r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_27r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_27r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_27r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_27r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_27r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_27r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_27r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_28_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_27r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_28 :
    hubcapFit theRedpart rf10 p10_27r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_28_1, c10_28_2, c10_28_3, c10_28_4, c10_28_5, c10_28_6, c10_28_7, c10_28_8, c10_28_9, c10_28_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_39r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_39r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_39r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_39r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_40_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_39r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_40 :
    hubcapFit theRedpart rf10 p10_39r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_40_1, c10_40_2, c10_40_3, c10_40_4, c10_40_5, c10_40_6, c10_40_7, c10_40_8, c10_40_9, c10_40_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_48r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_48r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_48r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_48r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_48r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_48r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_48r) (hubSubn 10 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_49_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_48r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_49 :
    hubcapFit theRedpart rf10 p10_48r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_49_1, c10_49_2, c10_49_3, c10_49_4, c10_49_5, c10_49_6, c10_49_7, c10_49_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_48l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_48l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_48l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_50_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_48l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_50 :
    hubcapFit theRedpart rf10 p10_48l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_50_1, c10_50_2, c10_50_3, c10_50_4, c10_50_5, c10_50_6, c10_50_7, c10_50_8, c10_50_9, c10_50_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_46l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_46l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_46l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_46l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_53_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_46l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_53 :
    hubcapFit theRedpart rf10 p10_46l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_53_1, c10_53_2, c10_53_3, c10_53_4, c10_53_5, c10_53_6, c10_53_7, c10_53_8, c10_53_9, c10_53_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_43l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_43l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_43l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_43l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_56_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_43l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_56 :
    hubcapFit theRedpart rf10 p10_43l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_56_1, c10_56_2, c10_56_3, c10_56_4, c10_56_5, c10_56_6, c10_56_7, c10_56_8, c10_56_9, c10_56_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_42l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_42l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_42l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_42l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_58_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_42l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_58 :
    hubcapFit theRedpart rf10 p10_42l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_58_1, c10_58_2, c10_58_3, c10_58_4, c10_58_5, c10_58_6, c10_58_7, c10_58_8, c10_58_9, c10_58_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_35l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_35l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_35l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_35l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_35l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_35l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_35l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_35l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_35l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_61_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_35l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_61 :
    hubcapFit theRedpart rf10 p10_35l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_61_1, c10_61_2, c10_61_3, c10_61_4, c10_61_5, c10_61_6, c10_61_7, c10_61_8, c10_61_9, c10_61_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_63l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_63l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_63l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_63l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_63l) (hubSubn 10 4 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_63l) (hubSubn 10 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_64_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_63l) (hubSubn 10 9 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_64 :
    hubcapFit theRedpart rf10 p10_63l
    (Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 6 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_64_1, c10_64_2, c10_64_3, c10_64_4, c10_64_5, c10_64_6, c10_64_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_63r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_63r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_63r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_63r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 0 p10_63r) (hubSubn 10 4 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_63r) (hubSubn 10 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_66_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 6 p10_63r) (hubSubn 10 9 6) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_66 :
    hubcapFit theRedpart rf10 p10_63r
    (Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 6 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 6 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_66_1, c10_66_2, c10_66_3, c10_66_4, c10_66_5, c10_66_6, c10_66_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_33l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_33l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_33l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_33l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_33l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_33l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_69_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_33l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_69 :
    hubcapFit theRedpart rf10 p10_33l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_69_1, c10_69_2, c10_69_3, c10_69_4, c10_69_5, c10_69_6, c10_69_7, c10_69_8, c10_69_9, c10_69_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_32l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_32l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_32l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_32l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_32l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_32l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_71_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_32l) (hubSubn 10 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_71 :
    hubcapFit theRedpart rf10 p10_32l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_71_1, c10_71_2, c10_71_3, c10_71_4, c10_71_5, c10_71_6, c10_71_7, c10_71_8, c10_71_9]

end FourColor

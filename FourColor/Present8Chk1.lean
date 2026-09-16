import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_41r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_41r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_41r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_41r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_41r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_42_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_41r) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_42 :
    hubcapFit theRedpart rf8 p8_41r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_42_1, c8_42_2, c8_42_3, c8_42_4, c8_42_5, c8_42_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_41l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_41l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_41l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_41l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_41l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_43_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_41l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_43 :
    hubcapFit theRedpart rf8 p8_41l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_43_1, c8_43_2, c8_43_3, c8_43_4, c8_43_5, c8_43_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_39l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_39l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_39l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_39l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_39l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_45_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_39l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_45 :
    hubcapFit theRedpart rf8 p8_39l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_45_1, c8_45_2, c8_45_3, c8_45_4, c8_45_5, c8_45_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_47_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_37l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_47_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_37l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_47_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_37l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_47_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_37l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_47_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_37l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_47 :
    hubcapFit theRedpart rf8 p8_37l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_47_1, c8_47_2, c8_47_3, c8_47_4, c8_47_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_49_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_36l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_49_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_36l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_49_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_36l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_49_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_36l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_49_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_36l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_49 :
    hubcapFit theRedpart rf8 p8_36l
    (Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_49_1, c8_49_2, c8_49_3, c8_49_4, c8_49_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_35l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_35l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_35l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_35l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_35l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_50_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_35l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_50 :
    hubcapFit theRedpart rf8 p8_35l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_50_1, c8_50_2, c8_50_3, c8_50_4, c8_50_5, c8_50_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_34l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_34l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_34l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_34l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_34l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_52_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_34l) (hubSubn 8 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_52 :
    hubcapFit theRedpart rf8 p8_34l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_52_1, c8_52_2, c8_52_3, c8_52_4, c8_52_5, c8_52_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_33l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_33l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_33l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_33l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_33l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_53_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_33l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_53 :
    hubcapFit theRedpart rf8 p8_33l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_53_1, c8_53_2, c8_53_3, c8_53_4, c8_53_5, c8_53_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_68r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_68r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_68r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_68r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_68r) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_69_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_68r) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_69 :
    hubcapFit theRedpart rf8 p8_68r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_69_1, c8_69_2, c8_69_3, c8_69_4, c8_69_5, c8_69_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_70_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_68l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_70_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_68l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_70_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_68l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_70_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_68l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_70_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_68l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_70 :
    hubcapFit theRedpart rf8 p8_68l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_70_1, c8_70_2, c8_70_3, c8_70_4, c8_70_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_67l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_67l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_67l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_67l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_67l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_67l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_67l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_72_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_67l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_72 :
    hubcapFit theRedpart rf8 p8_67l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_72_1, c8_72_2, c8_72_3, c8_72_4, c8_72_5, c8_72_6, c8_72_7, c8_72_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_66l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_66l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_66l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_66l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_66l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_74_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_66l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_74 :
    hubcapFit theRedpart rf8 p8_66l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_74_1, c8_74_2, c8_74_3, c8_74_4, c8_74_5, c8_74_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_65l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_65l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_65l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_65l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_65l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_75_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_65l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_75 :
    hubcapFit theRedpart rf8 p8_65l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_75_1, c8_75_2, c8_75_3, c8_75_4, c8_75_5, c8_75_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_64l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_64l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_64l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_64l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_64l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_77_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_64l) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_77 :
    hubcapFit theRedpart rf8 p8_64l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_77_1, c8_77_2, c8_77_3, c8_77_4, c8_77_5, c8_77_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_63l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_63l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_63l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_63l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_63l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_63l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_63l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_78_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_63l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_78 :
    hubcapFit theRedpart rf8 p8_63l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_78_1, c8_78_2, c8_78_3, c8_78_4, c8_78_5, c8_78_6, c8_78_7, c8_78_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_62l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_62l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_62l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_62l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_62l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_62l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_80_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_62l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_80 :
    hubcapFit theRedpart rf8 p8_62l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 0 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_80_1, c8_80_2, c8_80_3, c8_80_4, c8_80_5, c8_80_6, c8_80_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_61l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_61l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_61l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_61l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_61l) (hubSubn 8 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_82_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_61l) (hubSubn 8 7 6) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_82 :
    hubcapFit theRedpart rf8 p8_61l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 6 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_82_1, c8_82_2, c8_82_3, c8_82_4, c8_82_5, c8_82_6]

end FourColor

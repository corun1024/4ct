import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 12 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_656l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_656l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_656l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_682_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_656l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_682 :
    hubcapFit theRedpart rf7 p7_656l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_682_1, c7_682_2, c7_682_3, c7_682_4, c7_682_5, c7_682_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_655l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_655l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_655l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_655l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_655l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_655l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_683_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_655l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_683 :
    hubcapFit theRedpart rf7 p7_655l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_683_1, c7_683_2, c7_683_3, c7_683_4, c7_683_5, c7_683_6, c7_683_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_654l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_685_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_654l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_685 :
    hubcapFit theRedpart rf7 p7_654l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_685_1, c7_685_2, c7_685_3, c7_685_4, c7_685_5, c7_685_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_686_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_653l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_686_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_653l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_686_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_653l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_686_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_653l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_686_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_653l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_686 :
    hubcapFit theRedpart rf7 p7_653l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_686_1, c7_686_2, c7_686_3, c7_686_4, c7_686_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_652l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_652l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_652l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_652l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_652l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_652l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_688_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_652l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_688 :
    hubcapFit theRedpart rf7 p7_652l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_688_1, c7_688_2, c7_688_3, c7_688_4, c7_688_5, c7_688_6, c7_688_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_651l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_651l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_651l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_651l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_651l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_690_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_651l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_690 :
    hubcapFit theRedpart rf7 p7_651l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_690_1, c7_690_2, c7_690_3, c7_690_4, c7_690_5, c7_690_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_696r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_696r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_696r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_696r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_697_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_696r) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_697 :
    hubcapFit theRedpart rf7 p7_696r
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_697_1, c7_697_2, c7_697_3, c7_697_4, c7_697_5, c7_697_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_696l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_696l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_696l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_698_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_696l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_698 :
    hubcapFit theRedpart rf7 p7_696l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_698_1, c7_698_2, c7_698_3, c7_698_4, c7_698_5, c7_698_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_700_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_695l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_700 :
    hubcapFit theRedpart rf7 p7_695l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_700_1, c7_700_2, c7_700_3, c7_700_4, c7_700_5, c7_700_6, c7_700_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_694l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_694l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_694l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_702_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_694l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_702 :
    hubcapFit theRedpart rf7 p7_694l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_702_1, c7_702_2, c7_702_3, c7_702_4, c7_702_5, c7_702_6, c7_702_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_693l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_693l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_693l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_693l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_693l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_704_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_693l) (hubSubn 7 3 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_704 :
    hubcapFit theRedpart rf7 p7_693l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_704_1, c7_704_2, c7_704_3, c7_704_4, c7_704_5, c7_704_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_692l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_692l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_692l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_705_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_692l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_705 :
    hubcapFit theRedpart rf7 p7_692l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_705_1, c7_705_2, c7_705_3, c7_705_4, c7_705_5, c7_705_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_718r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_718r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_718r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_718r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_718r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_718r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_719_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_718r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_719 :
    hubcapFit theRedpart rf7 p7_718r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_719_1, c7_719_2, c7_719_3, c7_719_4, c7_719_5, c7_719_6, c7_719_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_718l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_718l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_718l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_718l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_718l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_720_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_718l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_720 :
    hubcapFit theRedpart rf7 p7_718l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_720_1, c7_720_2, c7_720_3, c7_720_4, c7_720_5, c7_720_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_717l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_717l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_717l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_717l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_722_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_717l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_722 :
    hubcapFit theRedpart rf7 p7_717l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_722_1, c7_722_2, c7_722_3, c7_722_4, c7_722_5, c7_722_6, c7_722_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_716l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_716l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_716l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_716l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_724_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_724 :
    hubcapFit theRedpart rf7 p7_716l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_724_1, c7_724_2, c7_724_3, c7_724_4, c7_724_5, c7_724_6, c7_724_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_715l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_715l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_715l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_715l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_726_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_715l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_726 :
    hubcapFit theRedpart rf7 p7_715l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_726_1, c7_726_2, c7_726_3, c7_726_4, c7_726_5, c7_726_6]

end FourColor

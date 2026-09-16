import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 2 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_29l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_29l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_29l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_29l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_29l) (hubSubn 9 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_76_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_29l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_76 :
    hubcapFit theRedpart rf9 p9_29l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 6 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_76_1, c9_76_2, c9_76_3, c9_76_4, c9_76_5, c9_76_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_28l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_28l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_28l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_28l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_28l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_77_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_28l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_77 :
    hubcapFit theRedpart rf9 p9_28l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_77_1, c9_77_2, c9_77_3, c9_77_4, c9_77_5, c9_77_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_27l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_27l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_27l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_27l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_27l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_27l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_79_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_27l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_79 :
    hubcapFit theRedpart rf9 p9_27l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_79_1, c9_79_2, c9_79_3, c9_79_4, c9_79_5, c9_79_6, c9_79_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_26l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_26l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_26l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_81_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_26l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_81 :
    hubcapFit theRedpart rf9 p9_26l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_81_1, c9_81_2, c9_81_3, c9_81_4, c9_81_5, c9_81_6, c9_81_7, c9_81_8, c9_81_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_25l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_25l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_25l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_25l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_25l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_25l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_83_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_25l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_83 :
    hubcapFit theRedpart rf9 p9_25l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_83_1, c9_83_2, c9_83_3, c9_83_4, c9_83_5, c9_83_6, c9_83_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_105r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_105r) (hubSubn 9 7 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_105r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_106_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_105r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_106 :
    hubcapFit theRedpart rf9 p9_105r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 4 <|
     Hubcap.two 1 7 7 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_106_1, c9_106_2, c9_106_3, c9_106_4, c9_106_5, c9_106_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_105l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_105l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_105l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_105l) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_105l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_107_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_105l) (hubSubn 9 7 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_107 :
    hubcapFit theRedpart rf9 p9_105l
    (Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 7 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_107_1, c9_107_2, c9_107_3, c9_107_4, c9_107_5, c9_107_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_109_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_104l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_109_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_104l) (hubSubn 9 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_109_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_104l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_109_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_104l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_109_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 7 p9_104l) (hubSubn 9 8 7) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_109 :
    hubcapFit theRedpart rf9 p9_104l
    (Hubcap.one 1 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 7 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_109_1, c9_109_2, c9_109_3, c9_109_4, c9_109_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_110_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_103l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_110_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_103l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_110_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_103l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_110_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_103l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_110_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_103l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_110 :
    hubcapFit theRedpart rf9 p9_103l
    (Hubcap.one 3 3 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_110_1, c9_110_2, c9_110_3, c9_110_4, c9_110_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_102l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_102l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_102l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_102l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_102l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_102l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_112_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_102l) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_112 :
    hubcapFit theRedpart rf9 p9_102l
    (Hubcap.one 0 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_112_1, c9_112_2, c9_112_3, c9_112_4, c9_112_5, c9_112_6, c9_112_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_100l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_100l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_100l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_100l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_100l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_114_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_100l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_114 :
    hubcapFit theRedpart rf9 p9_100l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_114_1, c9_114_2, c9_114_3, c9_114_4, c9_114_5, c9_114_6, c9_114_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_99l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_99l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_99l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_99l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_99l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_99l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_116_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_99l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_116 :
    hubcapFit theRedpart rf9 p9_99l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_116_1, c9_116_2, c9_116_3, c9_116_4, c9_116_5, c9_116_6, c9_116_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_98l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_98l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_98l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_98l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_98l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_98l) (hubSubn 9 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_118_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_98l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_118 :
    hubcapFit theRedpart rf9 p9_98l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_118_1, c9_118_2, c9_118_3, c9_118_4, c9_118_5, c9_118_6, c9_118_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_97l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_97l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_97l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_97l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_97l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_120_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_97l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_120 :
    hubcapFit theRedpart rf9 p9_97l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 7 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_120_1, c9_120_2, c9_120_3, c9_120_4, c9_120_5, c9_120_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_96l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_96l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_96l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_96l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_96l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_96l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_121_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_96l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_121 :
    hubcapFit theRedpart rf9 p9_96l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_121_1, c9_121_2, c9_121_3, c9_121_4, c9_121_5, c9_121_6, c9_121_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_95l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_95l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_95l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_95l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_95l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_95l) (hubSubn 9 5 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_123_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_95l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_123 :
    hubcapFit theRedpart rf9 p9_95l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 4 5 7 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_123_1, c9_123_2, c9_123_3, c9_123_4, c9_123_5, c9_123_6, c9_123_7]

end FourColor

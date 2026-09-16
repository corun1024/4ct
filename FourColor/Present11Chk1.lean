import FourColor.Present11Defs
import FourColor.TheQuizTree

/-!
Translated from `present11.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 1 of the arity 11 presentation

One of 6 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_75r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_75r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_75r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_75r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_75r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_76_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_75r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_76 :
    hubcapFit theRedpart rf11 p11_75r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_76_1, c11_76_2, c11_76_3, c11_76_4, c11_76_5, c11_76_6, c11_76_7, c11_76_8, c11_76_9, c11_76_10, c11_76_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_80r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_80r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_80r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_80r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_80r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_81_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_80r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_81 :
    hubcapFit theRedpart rf11 p11_80r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_81_1, c11_81_2, c11_81_3, c11_81_4, c11_81_5, c11_81_6, c11_81_7, c11_81_8, c11_81_9, c11_81_10, c11_81_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_88r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_88r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_88r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_88r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_88r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_89_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_88r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_89 :
    hubcapFit theRedpart rf11 p11_88r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_89_1, c11_89_2, c11_89_3, c11_89_4, c11_89_5, c11_89_6, c11_89_7, c11_89_8, c11_89_9, c11_89_10, c11_89_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_93r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_93r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_93r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_93r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_93r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_94_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_93r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_94 :
    hubcapFit theRedpart rf11 p11_93r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_94_1, c11_94_2, c11_94_3, c11_94_4, c11_94_5, c11_94_6, c11_94_7, c11_94_8, c11_94_9, c11_94_10, c11_94_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_97r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_97r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_97r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_97r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_97r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_98_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_97r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_98 :
    hubcapFit theRedpart rf11 p11_97r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_98_1, c11_98_2, c11_98_3, c11_98_4, c11_98_5, c11_98_6, c11_98_7, c11_98_8, c11_98_9, c11_98_10, c11_98_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_105r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_106_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_105r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_106 :
    hubcapFit theRedpart rf11 p11_105r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_106_1, c11_106_2, c11_106_3, c11_106_4, c11_106_5, c11_106_6, c11_106_7, c11_106_8, c11_106_9, c11_106_10, c11_106_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_104l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_10 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_108_11 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_108 :
    hubcapFit theRedpart rf11 p11_104l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.one 10 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_108_1, c11_108_2, c11_108_3, c11_108_4, c11_108_5, c11_108_6, c11_108_7, c11_108_8, c11_108_9, c11_108_10, c11_108_11]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_103l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_110_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 8 p11_103l) (hubSubn 11 9 8) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_110 :
    hubcapFit theRedpart rf11 p11_103l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 8 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_110_1, c11_110_2, c11_110_3, c11_110_4, c11_110_5, c11_110_6, c11_110_7, c11_110_8, c11_110_9, c11_110_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_127r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_127r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 6 p11_127r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_127r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 9 p11_127r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_128_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 2 p11_127r) (hubSubn 11 4 2) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_128 :
    hubcapFit theRedpart rf11 p11_127r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 2 4 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_128_1, c11_128_2, c11_128_3, c11_128_4, c11_128_5, c11_128_6, c11_128_7, c11_128_8, c11_128_9, c11_128_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_1 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 0 p11_133r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_2 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 1 p11_133r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_3 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 2 p11_133r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_4 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 3 p11_133r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_5 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 4 p11_133r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_6 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 5 p11_133r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_7 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 7 p11_133r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_8 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 8 p11_133r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_9 :
    checkDbound2 theRedpart rf11
      (hubcapRot 11 10 p11_133r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c11_134_10 :
    check2Dbound2 theRedpart rf11
      (hubcapRot 11 6 p11_133r) (hubSubn 11 9 6) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f11_134 :
    hubcapFit theRedpart rf11 p11_133r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 10 4 <|
     Hubcap.two 6 9 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c11_134_1, c11_134_2, c11_134_3, c11_134_4, c11_134_5, c11_134_6, c11_134_7, c11_134_8, c11_134_9, c11_134_10]

end FourColor

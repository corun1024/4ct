import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 46 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2532l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2534_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2532l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2534 :
    hubcapFit theRedpart rf7 p7_2532l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2534_1, c7_2534_2, c7_2534_3, c7_2534_4, c7_2534_5, c7_2534_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2531l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2531l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2531l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2531l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2531l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2536_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2531l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2536 :
    hubcapFit theRedpart rf7 p7_2531l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2536_1, c7_2536_2, c7_2536_3, c7_2536_4, c7_2536_5, c7_2536_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2528l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2528l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2528l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2528l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2528l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2528l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2538_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2528l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2538 :
    hubcapFit theRedpart rf7 p7_2528l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2538_1, c7_2538_2, c7_2538_3, c7_2538_4, c7_2538_5, c7_2538_6, c7_2538_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2549_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2548r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2549_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2548r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2549_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2548r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2549_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2548r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2549_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2548r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2549 :
    hubcapFit theRedpart rf7 p7_2548r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2549_1, c7_2549_2, c7_2549_3, c7_2549_4, c7_2549_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2548l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2548l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2548l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2550_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2550 :
    hubcapFit theRedpart rf7 p7_2548l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2550_1, c7_2550_2, c7_2550_3, c7_2550_4, c7_2550_5, c7_2550_6, c7_2550_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2552_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2547l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2552_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2547l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2552_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2547l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2552_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2547l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2552_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2547l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2552 :
    hubcapFit theRedpart rf7 p7_2547l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2552_1, c7_2552_2, c7_2552_3, c7_2552_4, c7_2552_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2554_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2545l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2554_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2545l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2554_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2545l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2554_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2545l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2554_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2545l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2554 :
    hubcapFit theRedpart rf7 p7_2545l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2554_1, c7_2554_2, c7_2554_3, c7_2554_4, c7_2554_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2560_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2559r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2560_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2559r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2560_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2559r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2560_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2559r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2560_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2559r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2560 :
    hubcapFit theRedpart rf7 p7_2559r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2560_1, c7_2560_2, c7_2560_3, c7_2560_4, c7_2560_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2561_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2558l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2561_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2558l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2561_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2558l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2561_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2558l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2561_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2558l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2561 :
    hubcapFit theRedpart rf7 p7_2558l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2561_1, c7_2561_2, c7_2561_3, c7_2561_4, c7_2561_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2563_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2557l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2563_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2557l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2563_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2557l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2563_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2557l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2563_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2557l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2563 :
    hubcapFit theRedpart rf7 p7_2557l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2563_1, c7_2563_2, c7_2563_3, c7_2563_4, c7_2563_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2540l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2540l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2540l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2540l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2540l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2565_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2540l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2565 :
    hubcapFit theRedpart rf7 p7_2540l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2565_1, c7_2565_2, c7_2565_3, c7_2565_4, c7_2565_5, c7_2565_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2573_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2572r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2573_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2572r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2573_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2572r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2573_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2572r) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2573_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2572r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2573 :
    hubcapFit theRedpart rf7 p7_2572r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2573_1, c7_2573_2, c7_2573_3, c7_2573_4, c7_2573_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2572l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2572l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2572l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2572l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2572l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2574_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2572l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2574 :
    hubcapFit theRedpart rf7 p7_2572l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2574_1, c7_2574_2, c7_2574_3, c7_2574_4, c7_2574_5, c7_2574_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2576_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2576_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2571l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2576_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2571l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2576_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2571l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2576_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2571l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2576 :
    hubcapFit theRedpart rf7 p7_2571l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2576_1, c7_2576_2, c7_2576_3, c7_2576_4, c7_2576_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2577_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2577_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2570l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2577_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2577_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2570l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2577_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2570l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2577 :
    hubcapFit theRedpart rf7 p7_2570l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2577_1, c7_2577_2, c7_2577_3, c7_2577_4, c7_2577_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2582_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2581r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2582_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2581r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2582_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2581r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2582_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2581r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2582_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2581r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2582 :
    hubcapFit theRedpart rf7 p7_2581r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2582_1, c7_2582_2, c7_2582_3, c7_2582_4, c7_2582_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2580l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2580l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2580l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2580l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2580l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2583_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2580l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2583 :
    hubcapFit theRedpart rf7 p7_2580l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2583_1, c7_2583_2, c7_2583_3, c7_2583_4, c7_2583_5, c7_2583_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2585_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2579l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2585_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2579l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2585_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2579l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2585_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2579l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2585_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2579l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2585 :
    hubcapFit theRedpart rf7 p7_2579l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2585_1, c7_2585_2, c7_2585_3, c7_2585_4, c7_2585_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2567l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2567l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2567l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2567l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2567l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2587_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2567l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2587 :
    hubcapFit theRedpart rf7 p7_2567l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2587_1, c7_2587_2, c7_2587_3, c7_2587_4, c7_2587_5, c7_2587_6]

end FourColor

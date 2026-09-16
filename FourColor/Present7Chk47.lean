import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 47 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2594r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2594r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2594r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2594r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2594r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2595_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2595 :
    hubcapFit theRedpart rf7 p7_2594r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2595_1, c7_2595_2, c7_2595_3, c7_2595_4, c7_2595_5, c7_2595_6, c7_2595_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2596_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2596_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2596_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2594l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2596_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2594l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2596_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2594l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2596 :
    hubcapFit theRedpart rf7 p7_2594l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2596_1, c7_2596_2, c7_2596_3, c7_2596_4, c7_2596_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2593l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2593l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2598_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2593l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2598 :
    hubcapFit theRedpart rf7 p7_2593l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2598_1, c7_2598_2, c7_2598_3, c7_2598_4, c7_2598_5, c7_2598_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2599_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2599_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2599_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2592l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2599_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2592l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2599_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2592l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2599 :
    hubcapFit theRedpart rf7 p7_2592l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 (-1) <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2599_1, c7_2599_2, c7_2599_3, c7_2599_4, c7_2599_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2603r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2603r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2603r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2604_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2603r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2604 :
    hubcapFit theRedpart rf7 p7_2603r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2604_1, c7_2604_2, c7_2604_3, c7_2604_4, c7_2604_5, c7_2604_6, c7_2604_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2605_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2605_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2605_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2603l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2605_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2603l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2605_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2603l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2605 :
    hubcapFit theRedpart rf7 p7_2603l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2605_1, c7_2605_2, c7_2605_3, c7_2605_4, c7_2605_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2602l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2602l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2607_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2602l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2607 :
    hubcapFit theRedpart rf7 p7_2602l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2607_1, c7_2607_2, c7_2607_3, c7_2607_4, c7_2607_5, c7_2607_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2608_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2601l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2608_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2601l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2608_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2601l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2608_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2601l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2608_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2601l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2608 :
    hubcapFit theRedpart rf7 p7_2601l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2608_1, c7_2608_2, c7_2608_3, c7_2608_4, c7_2608_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2611_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2610r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2611_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2610r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2611_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2610r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2611_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2610r) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2611_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2610r) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2611 :
    hubcapFit theRedpart rf7 p7_2610r
    (Hubcap.one 0 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2611_1, c7_2611_2, c7_2611_3, c7_2611_4, c7_2611_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2612_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2610l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2612_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2610l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2612_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2610l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2612_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2610l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2612_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2610l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2612 :
    hubcapFit theRedpart rf7 p7_2610l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2612_1, c7_2612_2, c7_2612_3, c7_2612_4, c7_2612_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2625r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2625r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2625r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2625r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2625r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2626_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2625r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2626 :
    hubcapFit theRedpart rf7 p7_2625r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2626_1, c7_2626_2, c7_2626_3, c7_2626_4, c7_2626_5, c7_2626_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2625l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2625l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2625l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2625l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2627_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2627 :
    hubcapFit theRedpart rf7 p7_2625l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2627_1, c7_2627_2, c7_2627_3, c7_2627_4, c7_2627_5, c7_2627_6, c7_2627_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2630_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2629r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2630_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2629r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2630_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2629r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2630_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2629r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2630_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2629r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2630 :
    hubcapFit theRedpart rf7 p7_2629r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2630_1, c7_2630_2, c7_2630_3, c7_2630_4, c7_2630_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2629l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2629l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2629l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2631_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2629l) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2631 :
    hubcapFit theRedpart rf7 p7_2629l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2631_1, c7_2631_2, c7_2631_3, c7_2631_4, c7_2631_5, c7_2631_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2635r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2635r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2635r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2635r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_2635r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2636_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2635r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2636 :
    hubcapFit theRedpart rf7 p7_2635r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2636_1, c7_2636_2, c7_2636_3, c7_2636_4, c7_2636_5, c7_2636_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2635l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2635l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2635l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2637_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2635l) (hubSubn 7 6 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2637 :
    hubcapFit theRedpart rf7 p7_2635l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 4 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2637_1, c7_2637_2, c7_2637_3, c7_2637_4, c7_2637_5, c7_2637_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2639_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2634l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2639_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2634l) (hubSubn 7 4 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2639_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2634l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2639_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2634l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2639 :
    hubcapFit theRedpart rf7 p7_2634l
    (Hubcap.one 5 0 <|
     Hubcap.two 0 4 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2639_1, c7_2639_2, c7_2639_3, c7_2639_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_2633l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_2633l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_2633l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_2633l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_2633l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_2640_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_2633l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_2640 :
    hubcapFit theRedpart rf7 p7_2633l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_2640_1, c7_2640_2, c7_2640_3, c7_2640_4, c7_2640_5, c7_2640_6]

end FourColor

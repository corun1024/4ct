import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 13 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_616l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_616l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_616l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_616l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_616l) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_646_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_616l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_646 :
    hubcapFit theRedpart rf8 p8_616l
    (Hubcap.one 0 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_646_1, c8_646_2, c8_646_3, c8_646_4, c8_646_5, c8_646_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_615l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_615l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_615l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_615l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_615l) (hubSubn 8 6 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_647_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_615l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_647 :
    hubcapFit theRedpart rf8 p8_615l
    (Hubcap.one 0 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 3 6 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_647_1, c8_647_2, c8_647_3, c8_647_4, c8_647_5, c8_647_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_652r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_652r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_652r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_652r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_652r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_652r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_653_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_652r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_653 :
    hubcapFit theRedpart rf8 p8_652r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_653_1, c8_653_2, c8_653_3, c8_653_4, c8_653_5, c8_653_6, c8_653_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_656_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_613l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_656_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_613l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_656_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_613l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_656_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_613l) (hubSubn 8 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_656_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_613l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_656 :
    hubcapFit theRedpart rf8 p8_613l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_656_1, c8_656_2, c8_656_3, c8_656_4, c8_656_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_612l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_612l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_612l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_612l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_612l) (hubSubn 8 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_657_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_612l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_657 :
    hubcapFit theRedpart rf8 p8_612l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.two 4 7 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_657_1, c8_657_2, c8_657_3, c8_657_4, c8_657_5, c8_657_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_671_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_670r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_671_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_670r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_671_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_670r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_671_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_670r) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_671_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_670r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_671 :
    hubcapFit theRedpart rf8 p8_670r
    (Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_671_1, c8_671_2, c8_671_3, c8_671_4, c8_671_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_672_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_670l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_672_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_670l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_672_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_670l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_672_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_670l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_672_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_670l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_672 :
    hubcapFit theRedpart rf8 p8_670l
    (Hubcap.one 0 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_672_1, c8_672_2, c8_672_3, c8_672_4, c8_672_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_669l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_674_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_669l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_674 :
    hubcapFit theRedpart rf8 p8_669l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_674_1, c8_674_2, c8_674_3, c8_674_4, c8_674_5, c8_674_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_675_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_675_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_675_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_668l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_675_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_668l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_675_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_668l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_675 :
    hubcapFit theRedpart rf8 p8_668l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_675_1, c8_675_2, c8_675_3, c8_675_4, c8_675_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_677_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_677_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_677_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_667l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_677_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_667l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_677_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_667l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_677 :
    hubcapFit theRedpart rf8 p8_667l
    (Hubcap.one 0 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_677_1, c8_677_2, c8_677_3, c8_677_4, c8_677_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_678_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_666l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_678_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_666l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_678_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_666l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_678_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_666l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_678_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_666l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_678 :
    hubcapFit theRedpart rf8 p8_666l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_678_1, c8_678_2, c8_678_3, c8_678_4, c8_678_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_680_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_665l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_680_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_680_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_665l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_680_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_665l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_680_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_665l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_680 :
    hubcapFit theRedpart rf8 p8_665l
    (Hubcap.one 0 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_680_1, c8_680_2, c8_680_3, c8_680_4, c8_680_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_664l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_681_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_664l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_681 :
    hubcapFit theRedpart rf8 p8_664l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_681_1, c8_681_2, c8_681_3, c8_681_4, c8_681_5, c8_681_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_690r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_690r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_690r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_690r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_690r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_691_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_690r) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_691 :
    hubcapFit theRedpart rf8 p8_690r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_691_1, c8_691_2, c8_691_3, c8_691_4, c8_691_5, c8_691_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_692_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_690l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_692_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_690l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_692_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_690l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_692_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_690l) (hubSubn 8 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_692_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_690l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_692 :
    hubcapFit theRedpart rf8 p8_690l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_692_1, c8_692_2, c8_692_3, c8_692_4, c8_692_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_689l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_689l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_689l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_689l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_694_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_689l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_694 :
    hubcapFit theRedpart rf8 p8_689l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_694_1, c8_694_2, c8_694_3, c8_694_4, c8_694_5, c8_694_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_688l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_688l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_695_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_688l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_695 :
    hubcapFit theRedpart rf8 p8_688l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_695_1, c8_695_2, c8_695_3, c8_695_4, c8_695_5, c8_695_6, c8_695_7, c8_695_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_687l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_687l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_687l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_687l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_697_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_687l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_697 :
    hubcapFit theRedpart rf8 p8_687l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_697_1, c8_697_2, c8_697_3, c8_697_4, c8_697_5, c8_697_6, c8_697_7]

end FourColor

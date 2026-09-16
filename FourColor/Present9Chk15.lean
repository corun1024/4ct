import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 15 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_630l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_630l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_661_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_630l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_661 :
    hubcapFit theRedpart rf9 p9_630l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_661_1, c9_661_2, c9_661_3, c9_661_4, c9_661_5, c9_661_6, c9_661_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_663_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_629l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_663 :
    hubcapFit theRedpart rf9 p9_629l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_663_1, c9_663_2, c9_663_3, c9_663_4, c9_663_5, c9_663_6, c9_663_7, c9_663_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_665_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_628l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_665 :
    hubcapFit theRedpart rf9 p9_628l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_665_1, c9_665_2, c9_665_3, c9_665_4, c9_665_5, c9_665_6, c9_665_7, c9_665_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_560l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_560l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_560l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_668_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_560l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_668 :
    hubcapFit theRedpart rf9 p9_560l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 0 <|
     Hubcap.one 8 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_668_1, c9_668_2, c9_668_3, c9_668_4, c9_668_5, c9_668_6, c9_668_7, c9_668_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_559l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_559l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_559l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_670_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_559l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_670 :
    hubcapFit theRedpart rf9 p9_559l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_670_1, c9_670_2, c9_670_3, c9_670_4, c9_670_5, c9_670_6, c9_670_7, c9_670_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_558l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_558l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_558l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_558l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_672_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_558l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_672 :
    hubcapFit theRedpart rf9 p9_558l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_672_1, c9_672_2, c9_672_3, c9_672_4, c9_672_5, c9_672_6, c9_672_7, c9_672_8, c9_672_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_557l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_557l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_557l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_557l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_674_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_557l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_674 :
    hubcapFit theRedpart rf9 p9_557l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_674_1, c9_674_2, c9_674_3, c9_674_4, c9_674_5, c9_674_6, c9_674_7, c9_674_8, c9_674_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_677l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_677l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_677l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_677l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_677l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_678_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_677l) (hubSubn 9 8 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_678 :
    hubcapFit theRedpart rf9 p9_677l
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_678_1, c9_678_2, c9_678_3, c9_678_4, c9_678_5, c9_678_6, c9_678_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_680l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_680l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_680l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_680l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_680l) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_681_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_680l) (hubSubn 9 8 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_681 :
    hubcapFit theRedpart rf9 p9_680l
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_681_1, c9_681_2, c9_681_3, c9_681_4, c9_681_5, c9_681_6, c9_681_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_680r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_680r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_680r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_680r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_680r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_680r) (hubSubn 9 7 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_683_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_680r) (hubSubn 9 8 2) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_683 :
    hubcapFit theRedpart rf9 p9_680r
    (Hubcap.one 1 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.two 0 7 8 <|
     Hubcap.two 2 8 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_683_1, c9_683_2, c9_683_3, c9_683_4, c9_683_5, c9_683_6, c9_683_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_687l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_687l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_687l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_687l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_688_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_687l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_688 :
    hubcapFit theRedpart rf9 p9_687l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_688_1, c9_688_2, c9_688_3, c9_688_4, c9_688_5, c9_688_6, c9_688_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_687r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_687r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_687r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_687r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_687r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_687r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_690_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_687r) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_690 :
    hubcapFit theRedpart rf9 p9_687r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_690_1, c9_690_2, c9_690_3, c9_690_4, c9_690_5, c9_690_6, c9_690_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_340l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_340l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_340l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_340l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_693_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_340l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_693 :
    hubcapFit theRedpart rf9 p9_340l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_693_1, c9_693_2, c9_693_3, c9_693_4, c9_693_5, c9_693_6, c9_693_7, c9_693_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_695l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_695l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_695l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_695l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_695l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_696_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_695l) (hubSubn 9 7 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_696 :
    hubcapFit theRedpart rf9 p9_695l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 4 6 8 <|
     Hubcap.two 5 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_696_1, c9_696_2, c9_696_3, c9_696_4, c9_696_5, c9_696_6, c9_696_7]

end FourColor

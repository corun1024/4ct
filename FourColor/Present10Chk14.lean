import FourColor.Present10Defs
import FourColor.TheQuizTree

/-!
Translated from `present10.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 14 of the arity 10 presentation

One of 24 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_651l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_651l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_651l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_651l) (hubSubn 10 5 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_652_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_651l) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_652 :
    hubcapFit theRedpart rf10 p10_651l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_652_1, c10_652_2, c10_652_3, c10_652_4, c10_652_5, c10_652_6, c10_652_7, c10_652_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_651r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_651r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_651r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_651r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_651r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_651r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 3 p10_651r) (hubSubn 10 5 3) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_654_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_651r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_654 :
    hubcapFit theRedpart rf10 p10_651r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 5 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_654_1, c10_654_2, c10_654_3, c10_654_4, c10_654_5, c10_654_6, c10_654_7, c10_654_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_632l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_632l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_632l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_657_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_632l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_657 :
    hubcapFit theRedpart rf10 p10_632l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_657_1, c10_657_2, c10_657_3, c10_657_4, c10_657_5, c10_657_6, c10_657_7, c10_657_8, c10_657_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_631l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_631l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_631l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_659_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_631l) (hubSubn 10 9 8) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_659 :
    hubcapFit theRedpart rf10 p10_631l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_659_1, c10_659_2, c10_659_3, c10_659_4, c10_659_5, c10_659_6, c10_659_7, c10_659_8, c10_659_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_630l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_630l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_630l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_630l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_661_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_630l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_661 :
    hubcapFit theRedpart rf10 p10_630l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_661_1, c10_661_2, c10_661_3, c10_661_4, c10_661_5, c10_661_6, c10_661_7, c10_661_8, c10_661_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_629l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_629l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_663_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_629l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_663 :
    hubcapFit theRedpart rf10 p10_629l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_663_1, c10_663_2, c10_663_3, c10_663_4, c10_663_5, c10_663_6, c10_663_7, c10_663_8, c10_663_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_690r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_690r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_690r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_690r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_690r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_690r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_690r) (hubSubn 10 3 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_691_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_690r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_691 :
    hubcapFit theRedpart rf10 p10_690r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 9 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_691_1, c10_691_2, c10_691_3, c10_691_4, c10_691_5, c10_691_6, c10_691_7, c10_691_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_690l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_690l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_690l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_690l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_5 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_690l) (hubSubn 10 3 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_6 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_690l) (hubSubn 10 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_692_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_690l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_692 :
    hubcapFit theRedpart rf10 p10_690l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 3 9 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_692_1, c10_692_2, c10_692_3, c10_692_4, c10_692_5, c10_692_6, c10_692_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_689l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_689l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_689l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_9 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_689l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_694_10 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_689l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_694 :
    hubcapFit theRedpart rf10 p10_689l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 5 <|
     Hubcap.one 9 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_694_1, c10_694_2, c10_694_3, c10_694_4, c10_694_5, c10_694_6, c10_694_7, c10_694_8, c10_694_9, c10_694_10]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_687l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_687l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_687l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_687l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_687l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_687l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_687l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_696_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_687l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_696 :
    hubcapFit theRedpart rf10 p10_687l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_696_1, c10_696_2, c10_696_3, c10_696_4, c10_696_5, c10_696_6, c10_696_7, c10_696_8, c10_696_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_686l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_7 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 8 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_8 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 9 p10_686l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_698_9 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_686l) (hubSubn 10 3 1) 9
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_698 :
    hubcapFit theRedpart rf10 p10_686l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.one 9 4 <|
     Hubcap.two 1 3 9 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_698_1, c10_698_2, c10_698_3, c10_698_4, c10_698_5, c10_698_6, c10_698_7, c10_698_8, c10_698_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_683l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_683l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 5 p10_683l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 6 p10_683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 1 p10_683l) (hubSubn 10 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_700_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_683l) (hubSubn 10 9 8) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_700 :
    hubcapFit theRedpart rf10 p10_683l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 5 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 8 9 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_700_1, c10_700_2, c10_700_3, c10_700_4, c10_700_5, c10_700_6, c10_700_7, c10_700_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_1 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 0 p10_704r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_2 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 1 p10_704r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_3 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 2 p10_704r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_4 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 3 p10_704r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_5 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 4 p10_704r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_6 :
    checkDbound2 theRedpart rf10
      (hubcapRot 10 7 p10_704r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_7 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 5 p10_704r) (hubSubn 10 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c10_705_8 :
    check2Dbound2 theRedpart rf10
      (hubcapRot 10 8 p10_704r) (hubSubn 10 9 8) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f10_705 :
    hubcapFit theRedpart rf10 p10_704r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.two 8 9 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c10_705_1, c10_705_2, c10_705_3, c10_705_4, c10_705_5, c10_705_6, c10_705_7, c10_705_8]

end FourColor

import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 12 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_586l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_586l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_586l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_586l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_586l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_586l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_586l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_595_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_586l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_595 :
    hubcapFit theRedpart rf8 p8_586l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_595_1, c8_595_2, c8_595_3, c8_595_4, c8_595_5, c8_595_6, c8_595_7, c8_595_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_574l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_574l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_597_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_574l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_597 :
    hubcapFit theRedpart rf8 p8_574l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_597_1, c8_597_2, c8_597_3, c8_597_4, c8_597_5, c8_597_6, c8_597_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_573l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_573l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_573l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_573l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_573l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_599_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_573l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_599 :
    hubcapFit theRedpart rf8 p8_573l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_599_1, c8_599_2, c8_599_3, c8_599_4, c8_599_5, c8_599_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_572l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_572l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_572l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_572l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_600_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_572l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_600 :
    hubcapFit theRedpart rf8 p8_572l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_600_1, c8_600_2, c8_600_3, c8_600_4, c8_600_5, c8_600_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_571l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_571l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_571l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_602_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_571l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_602 :
    hubcapFit theRedpart rf8 p8_571l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_602_1, c8_602_2, c8_602_3, c8_602_4, c8_602_5, c8_602_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_570l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_603_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_570l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_603 :
    hubcapFit theRedpart rf8 p8_570l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_603_1, c8_603_2, c8_603_3, c8_603_4, c8_603_5, c8_603_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_569l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_569l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_605_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_569l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_605 :
    hubcapFit theRedpart rf8 p8_569l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_605_1, c8_605_2, c8_605_3, c8_605_4, c8_605_5, c8_605_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_628r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_628r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_628r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_628r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_628r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_629_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_628r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_629 :
    hubcapFit theRedpart rf8 p8_628r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_629_1, c8_629_2, c8_629_3, c8_629_4, c8_629_5, c8_629_6, c8_629_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_628l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_628l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_630_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_628l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_630 :
    hubcapFit theRedpart rf8 p8_628l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_630_1, c8_630_2, c8_630_3, c8_630_4, c8_630_5, c8_630_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_627l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_627l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_627l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_627l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_627l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_627l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_632_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_627l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_632 :
    hubcapFit theRedpart rf8 p8_627l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_632_1, c8_632_2, c8_632_3, c8_632_4, c8_632_5, c8_632_6, c8_632_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_626l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_626l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_626l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_634_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_626l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_634 :
    hubcapFit theRedpart rf8 p8_626l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_634_1, c8_634_2, c8_634_3, c8_634_4, c8_634_5, c8_634_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_624l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_624l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_624l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_636_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_624l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_636 :
    hubcapFit theRedpart rf8 p8_624l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_636_1, c8_636_2, c8_636_3, c8_636_4, c8_636_5, c8_636_6, c8_636_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_621l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_621l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_621l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_621l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_621l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_621l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_638_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_621l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_638 :
    hubcapFit theRedpart rf8 p8_621l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_638_1, c8_638_2, c8_638_3, c8_638_4, c8_638_5, c8_638_6, c8_638_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_640_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_620l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_640_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_640_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_620l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_640_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_620l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_640_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_620l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_640 :
    hubcapFit theRedpart rf8 p8_620l
    (Hubcap.one 4 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_640_1, c8_640_2, c8_640_3, c8_640_4, c8_640_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_641_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_619l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_641_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_619l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_641_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_619l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_641_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_619l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_641_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_619l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_641 :
    hubcapFit theRedpart rf8 p8_619l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_641_1, c8_641_2, c8_641_3, c8_641_4, c8_641_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_618l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_618l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_618l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_618l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_643_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_618l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_643 :
    hubcapFit theRedpart rf8 p8_618l
    (Hubcap.one 3 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 4 5 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_643_1, c8_643_2, c8_643_3, c8_643_4, c8_643_5, c8_643_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_617l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_617l) (hubSubn 8 7 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_617l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_617l) (hubSubn 8 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_644_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_617l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_644 :
    hubcapFit theRedpart rf8 p8_617l
    (Hubcap.one 2 3 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_644_1, c8_644_2, c8_644_3, c8_644_4, c8_644_5, c8_644_6]

end FourColor

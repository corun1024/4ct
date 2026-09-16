import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 32 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1576_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1573r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1576_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1573r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1576_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1573r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1576_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1573r) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1576_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1573r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1576 :
    hubcapFit theRedpart rf8 p8_1573r
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1576_1, c8_1576_2, c8_1576_3, c8_1576_4, c8_1576_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1579_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1572r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1579_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1572r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1579_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1572r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1579_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1572r) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1579_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1572r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1579 :
    hubcapFit theRedpart rf8 p8_1572r
    (Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1579_1, c8_1579_2, c8_1579_3, c8_1579_4, c8_1579_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1594r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1594r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1594r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1594r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1595_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1594r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1595 :
    hubcapFit theRedpart rf8 p8_1594r
    (Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1595_1, c8_1595_2, c8_1595_3, c8_1595_4, c8_1595_5, c8_1595_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1594l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1594l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1594l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1596_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1594l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1596 :
    hubcapFit theRedpart rf8 p8_1594l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1596_1, c8_1596_2, c8_1596_3, c8_1596_4, c8_1596_5, c8_1596_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1593l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1593l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1598_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1593l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1598 :
    hubcapFit theRedpart rf8 p8_1593l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1598_1, c8_1598_2, c8_1598_3, c8_1598_4, c8_1598_5, c8_1598_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1592l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1592l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1592l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1599_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1592l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1599 :
    hubcapFit theRedpart rf8 p8_1592l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1599_1, c8_1599_2, c8_1599_3, c8_1599_4, c8_1599_5, c8_1599_6, c8_1599_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1591l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1591l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1591l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1591l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1591l) (hubSubn 8 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1601_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1591l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1601 :
    hubcapFit theRedpart rf8 p8_1591l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1601_1, c8_1601_2, c8_1601_3, c8_1601_4, c8_1601_5, c8_1601_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1590l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1590l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1590l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1590l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1590l) (hubSubn 8 6 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1602_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1590l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1602 :
    hubcapFit theRedpart rf8 p8_1590l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1602_1, c8_1602_2, c8_1602_3, c8_1602_4, c8_1602_5, c8_1602_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1609r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1609r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1609r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1609r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1609r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1609r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1610_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1609r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1610 :
    hubcapFit theRedpart rf8 p8_1609r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1610_1, c8_1610_2, c8_1610_3, c8_1610_4, c8_1610_5, c8_1610_6, c8_1610_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1609l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1609l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1611_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1609l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1611 :
    hubcapFit theRedpart rf8 p8_1609l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1611_1, c8_1611_2, c8_1611_3, c8_1611_4, c8_1611_5, c8_1611_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1608l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1608l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1608l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1613_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1608l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1613 :
    hubcapFit theRedpart rf8 p8_1608l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1613_1, c8_1613_2, c8_1613_3, c8_1613_4, c8_1613_5, c8_1613_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1606l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1606l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1606l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1606l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1606l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1606l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1615_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1606l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1615 :
    hubcapFit theRedpart rf8 p8_1606l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1615_1, c8_1615_2, c8_1615_3, c8_1615_4, c8_1615_5, c8_1615_6, c8_1615_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1618l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1619_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1618l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1619 :
    hubcapFit theRedpart rf8 p8_1618l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1619_1, c8_1619_2, c8_1619_3, c8_1619_4, c8_1619_5, c8_1619_6, c8_1619_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1618r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1618r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1618r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1618r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1618r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1618r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1621_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1618r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1621 :
    hubcapFit theRedpart rf8 p8_1618r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1621_1, c8_1621_2, c8_1621_3, c8_1621_4, c8_1621_5, c8_1621_6, c8_1621_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1617r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1617r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1617r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1617r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1617r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1617r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1624_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1617r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1624 :
    hubcapFit theRedpart rf8 p8_1617r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1624_1, c8_1624_2, c8_1624_3, c8_1624_4, c8_1624_5, c8_1624_6, c8_1624_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1629l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1629l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1630_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1629l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1630 :
    hubcapFit theRedpart rf8 p8_1629l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1630_1, c8_1630_2, c8_1630_3, c8_1630_4, c8_1630_5, c8_1630_6, c8_1630_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1629r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1629r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1629r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1629r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1629r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1629r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1632_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1629r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1632 :
    hubcapFit theRedpart rf8 p8_1629r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1632_1, c8_1632_2, c8_1632_3, c8_1632_4, c8_1632_5, c8_1632_6, c8_1632_7]

end FourColor

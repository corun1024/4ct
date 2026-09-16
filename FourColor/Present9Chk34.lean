import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 34 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1601l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1601l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1601l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1615_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1601l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1615 :
    hubcapFit theRedpart rf9 p9_1601l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1615_1, c9_1615_2, c9_1615_3, c9_1615_4, c9_1615_5, c9_1615_6, c9_1615_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1600l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1617_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1600l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1617 :
    hubcapFit theRedpart rf9 p9_1600l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1617_1, c9_1617_2, c9_1617_3, c9_1617_4, c9_1617_5, c9_1617_6, c9_1617_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1598l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1598l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1598l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1619_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1598l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1619 :
    hubcapFit theRedpart rf9 p9_1598l
    (Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1619_1, c9_1619_2, c9_1619_3, c9_1619_4, c9_1619_5, c9_1619_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1553l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1553l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1621_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1553l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1621 :
    hubcapFit theRedpart rf9 p9_1553l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1621_1, c9_1621_2, c9_1621_3, c9_1621_4, c9_1621_5, c9_1621_6, c9_1621_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1629r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1629r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1629r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1629r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1629r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1630_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1629r) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1630 :
    hubcapFit theRedpart rf9 p9_1629r
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1630_1, c9_1630_2, c9_1630_3, c9_1630_4, c9_1630_5, c9_1630_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1629l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1629l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1629l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1631_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1629l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1631 :
    hubcapFit theRedpart rf9 p9_1629l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1631_1, c9_1631_2, c9_1631_3, c9_1631_4, c9_1631_5, c9_1631_6, c9_1631_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1628l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1628l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1628l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1633_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1628l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1633 :
    hubcapFit theRedpart rf9 p9_1628l
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1633_1, c9_1633_2, c9_1633_3, c9_1633_4, c9_1633_5, c9_1633_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1638r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1638r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1639_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1638r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1639 :
    hubcapFit theRedpart rf9 p9_1638r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1639_1, c9_1639_2, c9_1639_3, c9_1639_4, c9_1639_5, c9_1639_6, c9_1639_7, c9_1639_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1635l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1635l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1635l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1635l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1641_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1635l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1641 :
    hubcapFit theRedpart rf9 p9_1635l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1641_1, c9_1641_2, c9_1641_3, c9_1641_4, c9_1641_5, c9_1641_6, c9_1641_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1634l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1634l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1634l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1634l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1634l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1643_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1634l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1643 :
    hubcapFit theRedpart rf9 p9_1634l
    (Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1643_1, c9_1643_2, c9_1643_3, c9_1643_4, c9_1643_5, c9_1643_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1626l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1626l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1626l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1626l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1645_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1626l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1645 :
    hubcapFit theRedpart rf9 p9_1626l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1645_1, c9_1645_2, c9_1645_3, c9_1645_4, c9_1645_5, c9_1645_6, c9_1645_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1625l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1625l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1647_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1625l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1647 :
    hubcapFit theRedpart rf9 p9_1625l
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1647_1, c9_1647_2, c9_1647_3, c9_1647_4, c9_1647_5, c9_1647_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1624l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1624l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1648_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1624l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1648 :
    hubcapFit theRedpart rf9 p9_1624l
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1648_1, c9_1648_2, c9_1648_3, c9_1648_4, c9_1648_5, c9_1648_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1623l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1623l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1623l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1650_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1623l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1650 :
    hubcapFit theRedpart rf9 p9_1623l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1650_1, c9_1650_2, c9_1650_3, c9_1650_4, c9_1650_5, c9_1650_6, c9_1650_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1551l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1551l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1551l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1652_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1551l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1652 :
    hubcapFit theRedpart rf9 p9_1551l
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1652_1, c9_1652_2, c9_1652_3, c9_1652_4, c9_1652_5, c9_1652_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1550l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1550l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1654_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1550l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1654 :
    hubcapFit theRedpart rf9 p9_1550l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1654_1, c9_1654_2, c9_1654_3, c9_1654_4, c9_1654_5, c9_1654_6, c9_1654_7]

end FourColor

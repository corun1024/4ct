import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 28 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1536r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1536r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1536r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1536r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1536r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1537_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1536r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1537 :
    hubcapFit theRedpart rf7 p7_1536r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1537_1, c7_1537_2, c7_1537_3, c7_1537_4, c7_1537_5, c7_1537_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1536l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1536l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1536l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1536l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1536l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1536l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1538_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1536l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1538 :
    hubcapFit theRedpart rf7 p7_1536l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1538_1, c7_1538_2, c7_1538_3, c7_1538_4, c7_1538_5, c7_1538_6, c7_1538_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1540_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1535l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1540_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1535l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1540_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1535l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1540_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1535l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1540_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1535l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1540 :
    hubcapFit theRedpart rf7 p7_1535l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1540_1, c7_1540_2, c7_1540_3, c7_1540_4, c7_1540_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1542_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1519l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1542_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1519l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1542_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1519l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1542_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1519l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1542_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1519l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1542 :
    hubcapFit theRedpart rf7 p7_1519l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1542_1, c7_1542_2, c7_1542_3, c7_1542_4, c7_1542_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1546_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1545r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1546_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1545r) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1546_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1545r) (hubSubn 7 4 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1546_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1545r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1546 :
    hubcapFit theRedpart rf7 p7_1545r
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 1 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1546_1, c7_1546_2, c7_1546_3, c7_1546_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1547_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1545l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1547_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1545l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1547_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1545l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1547_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1545l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1547_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1545l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1547 :
    hubcapFit theRedpart rf7 p7_1545l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1547_1, c7_1547_2, c7_1547_3, c7_1547_4, c7_1547_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1544l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1544l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1544l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1544l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1544l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1549_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1544l) (hubSubn 7 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1549 :
    hubcapFit theRedpart rf7 p7_1544l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1549_1, c7_1549_2, c7_1549_3, c7_1549_4, c7_1549_5, c7_1549_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1543l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1543l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1543l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1550_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1543l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1550 :
    hubcapFit theRedpart rf7 p7_1543l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1550_1, c7_1550_2, c7_1550_3, c7_1550_4, c7_1550_5, c7_1550_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1561_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1560r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1561_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1560r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1561_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1560r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1561_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1560r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1561_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1560r) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1561 :
    hubcapFit theRedpart rf7 p7_1560r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1561_1, c7_1561_2, c7_1561_3, c7_1561_4, c7_1561_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1562_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1560l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1562_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1560l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1562_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1560l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1562_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1560l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1562_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1560l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1562 :
    hubcapFit theRedpart rf7 p7_1560l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1562_1, c7_1562_2, c7_1562_3, c7_1562_4, c7_1562_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1559l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1559l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1559l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1559l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1559l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1559l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1564_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1559l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1564 :
    hubcapFit theRedpart rf7 p7_1559l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1564_1, c7_1564_2, c7_1564_3, c7_1564_4, c7_1564_5, c7_1564_6, c7_1564_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1566_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1557l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1566_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1557l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1566_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1557l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1566_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1557l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1566_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1557l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1566 :
    hubcapFit theRedpart rf7 p7_1557l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1566_1, c7_1566_2, c7_1566_3, c7_1566_4, c7_1566_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1571r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1571r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1571r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1571r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1571r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1572_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1571r) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1572 :
    hubcapFit theRedpart rf7 p7_1571r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1572_1, c7_1572_2, c7_1572_3, c7_1572_4, c7_1572_5, c7_1572_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1571l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1571l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1571l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1571l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1571l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1571l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1573_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1573 :
    hubcapFit theRedpart rf7 p7_1571l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1573_1, c7_1573_2, c7_1573_3, c7_1573_4, c7_1573_5, c7_1573_6, c7_1573_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1570l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1575_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1570l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1575 :
    hubcapFit theRedpart rf7 p7_1570l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1575_1, c7_1575_2, c7_1575_3, c7_1575_4, c7_1575_5, c7_1575_6, c7_1575_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1569l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1569l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1577_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1577 :
    hubcapFit theRedpart rf7 p7_1569l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1577_1, c7_1577_2, c7_1577_3, c7_1577_4, c7_1577_5, c7_1577_6, c7_1577_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1568l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1568l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1568l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1568l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1579_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1568l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1579 :
    hubcapFit theRedpart rf7 p7_1568l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1579_1, c7_1579_2, c7_1579_3, c7_1579_4, c7_1579_5, c7_1579_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1555l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1555l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1555l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1555l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1555l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1581_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1555l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1581 :
    hubcapFit theRedpart rf7 p7_1555l
    (Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1581_1, c7_1581_2, c7_1581_3, c7_1581_4, c7_1581_5, c7_1581_6]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 29 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1583r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1583r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1583r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1583r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1583r) (hubSubn 7 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1584_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1583r) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1584 :
    hubcapFit theRedpart rf7 p7_1583r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1584_1, c7_1584_2, c7_1584_3, c7_1584_4, c7_1584_5, c7_1584_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1585_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1585_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1583l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1585_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1585_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1583l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1585_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1583l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1585 :
    hubcapFit theRedpart rf7 p7_1583l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1585_1, c7_1585_2, c7_1585_3, c7_1585_4, c7_1585_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1587_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1582l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1587_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1582l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1587_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1582l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1587_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1582l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1587_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1582l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1587 :
    hubcapFit theRedpart rf7 p7_1582l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1587_1, c7_1587_2, c7_1587_3, c7_1587_4, c7_1587_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1601r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1601r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1601r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1601r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1601r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1602_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1601r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1602 :
    hubcapFit theRedpart rf7 p7_1601r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1602_1, c7_1602_2, c7_1602_3, c7_1602_4, c7_1602_5, c7_1602_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1606_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1605r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1606_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1605r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1606_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1605r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1606_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1605r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1606_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1605r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1606 :
    hubcapFit theRedpart rf7 p7_1605r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1606_1, c7_1606_2, c7_1606_3, c7_1606_4, c7_1606_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1607_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1605l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1607_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1605l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1607_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1605l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1607_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1605l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1607_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1605l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1607 :
    hubcapFit theRedpart rf7 p7_1605l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1607_1, c7_1607_2, c7_1607_3, c7_1607_4, c7_1607_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1609_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1604l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1609_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1604l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1609_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1604l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1609_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1604l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1609_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1604l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1609 :
    hubcapFit theRedpart rf7 p7_1604l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1609_1, c7_1609_2, c7_1609_3, c7_1609_4, c7_1609_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1611_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1597l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1611_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1597l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1611_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1597l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1611_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1597l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1611_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1597l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1611 :
    hubcapFit theRedpart rf7 p7_1597l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1611_1, c7_1611_2, c7_1611_3, c7_1611_4, c7_1611_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1596l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1596l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1596l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1596l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1596l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1612_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1596l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1612 :
    hubcapFit theRedpart rf7 p7_1596l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1612_1, c7_1612_2, c7_1612_3, c7_1612_4, c7_1612_5, c7_1612_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1595l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1595l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1595l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1614_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1595l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1614 :
    hubcapFit theRedpart rf7 p7_1595l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1614_1, c7_1614_2, c7_1614_3, c7_1614_4, c7_1614_5, c7_1614_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1620r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1620r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1620r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1620r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1620r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1621_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1620r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1621 :
    hubcapFit theRedpart rf7 p7_1620r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1621_1, c7_1621_2, c7_1621_3, c7_1621_4, c7_1621_5, c7_1621_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1623_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1618l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1623_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1618l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1623_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1618l) (hubSubn 7 4 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1623_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1618l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1623 :
    hubcapFit theRedpart rf7 p7_1618l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1623_1, c7_1623_2, c7_1623_3, c7_1623_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1617l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1617l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1617l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1617l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1617l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1624_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1617l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1624 :
    hubcapFit theRedpart rf7 p7_1617l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1624_1, c7_1624_2, c7_1624_3, c7_1624_4, c7_1624_5, c7_1624_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1626_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1626_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1616l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1626_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1626_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1616l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1626_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1616l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1626 :
    hubcapFit theRedpart rf7 p7_1616l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1626_1, c7_1626_2, c7_1626_3, c7_1626_4, c7_1626_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1615l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1615l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1615l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1627_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1627 :
    hubcapFit theRedpart rf7 p7_1615l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1627_1, c7_1627_2, c7_1627_3, c7_1627_4, c7_1627_5, c7_1627_6, c7_1627_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1636r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1636r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1636r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1636r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1636r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1637_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1636r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1637 :
    hubcapFit theRedpart rf7 p7_1636r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1637_1, c7_1637_2, c7_1637_3, c7_1637_4, c7_1637_5, c7_1637_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1636l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1636l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1636l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1636l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1636l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1638_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1636l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1638 :
    hubcapFit theRedpart rf7 p7_1636l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1638_1, c7_1638_2, c7_1638_3, c7_1638_4, c7_1638_5, c7_1638_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1635l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1635l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1635l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1635l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1635l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1640_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1635l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1640 :
    hubcapFit theRedpart rf7 p7_1635l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1640_1, c7_1640_2, c7_1640_3, c7_1640_4, c7_1640_5, c7_1640_6, c7_1640_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1645_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1644r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1645_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1644r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1645_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1644r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1645_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1644r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1645_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1644r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1645 :
    hubcapFit theRedpart rf7 p7_1644r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1645_1, c7_1645_2, c7_1645_3, c7_1645_4, c7_1645_5]

end FourColor

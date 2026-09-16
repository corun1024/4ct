import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 30 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1644l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1646_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1644l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1646 :
    hubcapFit theRedpart rf7 p7_1644l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1646_1, c7_1646_2, c7_1646_3, c7_1646_4, c7_1646_5, c7_1646_6, c7_1646_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1648_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1643l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1648_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1643l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1648_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1643l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1648_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1643l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1648_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1643l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1648 :
    hubcapFit theRedpart rf7 p7_1643l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1648_1, c7_1648_2, c7_1648_3, c7_1648_4, c7_1648_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1642l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1642l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1642l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1649_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1642l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1649 :
    hubcapFit theRedpart rf7 p7_1642l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1649_1, c7_1649_2, c7_1649_3, c7_1649_4, c7_1649_5, c7_1649_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1651_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1651_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1632l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1651_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1632l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1651_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1632l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1651_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1632l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1651 :
    hubcapFit theRedpart rf7 p7_1632l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1651_1, c7_1651_2, c7_1651_3, c7_1651_4, c7_1651_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1631l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1631l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1631l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1631l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1631l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1653_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1631l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1653 :
    hubcapFit theRedpart rf7 p7_1631l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 1 <|
     Hubcap.two 4 6 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1653_1, c7_1653_2, c7_1653_3, c7_1653_4, c7_1653_5, c7_1653_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1630l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1630l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1630l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1630l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1630l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1654_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1630l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1654 :
    hubcapFit theRedpart rf7 p7_1630l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1654_1, c7_1654_2, c7_1654_3, c7_1654_4, c7_1654_5, c7_1654_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1656_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1592l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1656_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1592l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1656_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1592l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1656_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1592l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1656_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1592l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1656 :
    hubcapFit theRedpart rf7 p7_1592l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1656_1, c7_1656_2, c7_1656_3, c7_1656_4, c7_1656_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1663r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1663r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1663r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1663r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1663r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1663r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1664_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1663r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1664 :
    hubcapFit theRedpart rf7 p7_1663r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1664_1, c7_1664_2, c7_1664_3, c7_1664_4, c7_1664_5, c7_1664_6, c7_1664_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1665_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1665_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1665_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1663l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1665_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1663l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1665_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1663l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1665 :
    hubcapFit theRedpart rf7 p7_1663l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1665_1, c7_1665_2, c7_1665_3, c7_1665_4, c7_1665_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1667_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1667_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1662l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1667_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1662l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1667_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1662l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1667 :
    hubcapFit theRedpart rf7 p7_1662l
    (Hubcap.one 5 2 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 1 6 5 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1667_1, c7_1667_2, c7_1667_3, c7_1667_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1668_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1661l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1668_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1661l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1668_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1668_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1661l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1668_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1661l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1668 :
    hubcapFit theRedpart rf7 p7_1661l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 1 6 4 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1668_1, c7_1668_2, c7_1668_3, c7_1668_4, c7_1668_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1670_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1660l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1670_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1660l) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1670_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1660l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1670_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1660l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1670 :
    hubcapFit theRedpart rf7 p7_1660l
    (Hubcap.one 0 2 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 3 1 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1670_1, c7_1670_2, c7_1670_3, c7_1670_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1659l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1659l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1659l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1671_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1659l) (hubSubn 7 3 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1671 :
    hubcapFit theRedpart rf7 p7_1659l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1671_1, c7_1671_2, c7_1671_3, c7_1671_4, c7_1671_5, c7_1671_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1673_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1658l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1673_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1658l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1673_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1658l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1673_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1658l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1673 :
    hubcapFit theRedpart rf7 p7_1658l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1673_1, c7_1673_2, c7_1673_3, c7_1673_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1675_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1590l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1675_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1590l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1675_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1590l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1675_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1590l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1675_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1590l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1675 :
    hubcapFit theRedpart rf7 p7_1590l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1675_1, c7_1675_2, c7_1675_3, c7_1675_4, c7_1675_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1676_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1589l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1676_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1589l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1676_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1589l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1676_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1589l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1676 :
    hubcapFit theRedpart rf7 p7_1589l
    (Hubcap.one 1 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1676_1, c7_1676_2, c7_1676_3, c7_1676_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1685_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1684r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1685_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1684r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1685_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1684r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1685_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1684r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1685_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1684r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1685 :
    hubcapFit theRedpart rf7 p7_1684r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1685_1, c7_1685_2, c7_1685_3, c7_1685_4, c7_1685_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1686_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1684l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1686_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1684l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1686_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1684l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1686_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1684l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1686_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1684l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1686 :
    hubcapFit theRedpart rf7 p7_1684l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1686_1, c7_1686_2, c7_1686_3, c7_1686_4, c7_1686_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1683l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1683l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1683l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1683l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1683l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1688_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1683l) (hubSubn 7 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1688 :
    hubcapFit theRedpart rf7 p7_1683l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1688_1, c7_1688_2, c7_1688_3, c7_1688_4, c7_1688_5, c7_1688_6]

end FourColor

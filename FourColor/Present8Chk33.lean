import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 33 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1628r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1628r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1628r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1628r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1635_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1628r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1635 :
    hubcapFit theRedpart rf8 p8_1628r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1635_1, c8_1635_2, c8_1635_3, c8_1635_4, c8_1635_5, c8_1635_6, c8_1635_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1639l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1639l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1639l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1639l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1639l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1640_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1639l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1640 :
    hubcapFit theRedpart rf8 p8_1639l
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1640_1, c8_1640_2, c8_1640_3, c8_1640_4, c8_1640_5, c8_1640_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1639r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1639r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1639r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1639r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1639r) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1642_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1639r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1642 :
    hubcapFit theRedpart rf8 p8_1639r
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1642_1, c8_1642_2, c8_1642_3, c8_1642_4, c8_1642_5, c8_1642_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1638r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1638r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1638r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1638r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1638r) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1645_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1638r) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1645 :
    hubcapFit theRedpart rf8 p8_1638r
    (Hubcap.one 5 2 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1645_1, c8_1645_2, c8_1645_3, c8_1645_4, c8_1645_5, c8_1645_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1656r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1656r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1656r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1656r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1657_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1656r) (hubSubn 8 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1657 :
    hubcapFit theRedpart rf8 p8_1656r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1657_1, c8_1657_2, c8_1657_3, c8_1657_4, c8_1657_5, c8_1657_6, c8_1657_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1656l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1656l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1658_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1658 :
    hubcapFit theRedpart rf8 p8_1656l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1658_1, c8_1658_2, c8_1658_3, c8_1658_4, c8_1658_5, c8_1658_6, c8_1658_7, c8_1658_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1655l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1655l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1655l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1655l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1655l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1660_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1655l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1660 :
    hubcapFit theRedpart rf8 p8_1655l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1660_1, c8_1660_2, c8_1660_3, c8_1660_4, c8_1660_5, c8_1660_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1654l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1654l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1654l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1654l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1661_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1654l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1661 :
    hubcapFit theRedpart rf8 p8_1654l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1661_1, c8_1661_2, c8_1661_3, c8_1661_4, c8_1661_5, c8_1661_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1663l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1664_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1663l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1664 :
    hubcapFit theRedpart rf8 p8_1663l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1664_1, c8_1664_2, c8_1664_3, c8_1664_4, c8_1664_5, c8_1664_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1663r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1663r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1663r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1663r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1663r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1666_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1663r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1666 :
    hubcapFit theRedpart rf8 p8_1663r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1666_1, c8_1666_2, c8_1666_3, c8_1666_4, c8_1666_5, c8_1666_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1652l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1652l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1652l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1652l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1652l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1669_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1652l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1669 :
    hubcapFit theRedpart rf8 p8_1652l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1669_1, c8_1669_2, c8_1669_3, c8_1669_4, c8_1669_5, c8_1669_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1671l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1672_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1671l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1672 :
    hubcapFit theRedpart rf8 p8_1671l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1672_1, c8_1672_2, c8_1672_3, c8_1672_4, c8_1672_5, c8_1672_6, c8_1672_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1671r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1671r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1671r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1671r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1671r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1671r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1674_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1671r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1674 :
    hubcapFit theRedpart rf8 p8_1671r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1674_1, c8_1674_2, c8_1674_3, c8_1674_4, c8_1674_5, c8_1674_6, c8_1674_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1678l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1678l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1679_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1678l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1679 :
    hubcapFit theRedpart rf8 p8_1678l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1679_1, c8_1679_2, c8_1679_3, c8_1679_4, c8_1679_5, c8_1679_6, c8_1679_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1678r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1678r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1678r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1678r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1681_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1678r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1681 :
    hubcapFit theRedpart rf8 p8_1678r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1681_1, c8_1681_2, c8_1681_3, c8_1681_4, c8_1681_5, c8_1681_6, c8_1681_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1677r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1677r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1677r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1677r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1677r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1677r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1684_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1677r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1684 :
    hubcapFit theRedpart rf8 p8_1677r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1684_1, c8_1684_2, c8_1684_3, c8_1684_4, c8_1684_5, c8_1684_6, c8_1684_7]

end FourColor

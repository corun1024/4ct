import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 34 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1688l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1688l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1688l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1689_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1688l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1689 :
    hubcapFit theRedpart rf8 p8_1688l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1689_1, c8_1689_2, c8_1689_3, c8_1689_4, c8_1689_5, c8_1689_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1688r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1688r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1688r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1688r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1688r) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1691_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1688r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1691 :
    hubcapFit theRedpart rf8 p8_1688r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1691_1, c8_1691_2, c8_1691_3, c8_1691_4, c8_1691_5, c8_1691_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1687r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1687r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1687r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1687r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1687r) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1694_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1687r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1694 :
    hubcapFit theRedpart rf8 p8_1687r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1694_1, c8_1694_2, c8_1694_3, c8_1694_4, c8_1694_5, c8_1694_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1584l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1584l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1584l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1584l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1698_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1584l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1698 :
    hubcapFit theRedpart rf8 p8_1584l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1698_1, c8_1698_2, c8_1698_3, c8_1698_4, c8_1698_5, c8_1698_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1583l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1583l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1583l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1583l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1700_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1583l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1700 :
    hubcapFit theRedpart rf8 p8_1583l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1700_1, c8_1700_2, c8_1700_3, c8_1700_4, c8_1700_5, c8_1700_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1703_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1703_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1702l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1703_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1702l) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1703_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1702l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1703_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1702l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1703 :
    hubcapFit theRedpart rf8 p8_1702l
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1703_1, c8_1703_2, c8_1703_3, c8_1703_4, c8_1703_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1705_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1702r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1705_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1702r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1705_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1702r) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1705_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1702r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1705_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1702r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1705 :
    hubcapFit theRedpart rf8 p8_1702r
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1705_1, c8_1705_2, c8_1705_3, c8_1705_4, c8_1705_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1708_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1708_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1701r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1708_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1701r) (hubSubn 8 3 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1708_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1701r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1708_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1701r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1708 :
    hubcapFit theRedpart rf8 p8_1701r
    (Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1708_1, c8_1708_2, c8_1708_3, c8_1708_4, c8_1708_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1713l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1713l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1714_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1713l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1714 :
    hubcapFit theRedpart rf8 p8_1713l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1714_1, c8_1714_2, c8_1714_3, c8_1714_4, c8_1714_5, c8_1714_6, c8_1714_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1713r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1713r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1713r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1713r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1713r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1713r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1716_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1713r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1716 :
    hubcapFit theRedpart rf8 p8_1713r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1716_1, c8_1716_2, c8_1716_3, c8_1716_4, c8_1716_5, c8_1716_6, c8_1716_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1712r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1712r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1712r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1712r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1712r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1712r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1719_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1712r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1719 :
    hubcapFit theRedpart rf8 p8_1712r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1719_1, c8_1719_2, c8_1719_3, c8_1719_4, c8_1719_5, c8_1719_6, c8_1719_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1741r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1741r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1741r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1741r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1741r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1741r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1742_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1741r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1742 :
    hubcapFit theRedpart rf8 p8_1741r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1742_1, c8_1742_2, c8_1742_3, c8_1742_4, c8_1742_5, c8_1742_6, c8_1742_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1741l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1741l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1741l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1741l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1743_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1743 :
    hubcapFit theRedpart rf8 p8_1741l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1743_1, c8_1743_2, c8_1743_3, c8_1743_4, c8_1743_5, c8_1743_6, c8_1743_7, c8_1743_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1739l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1739l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1739l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1739l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1745_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1739l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1745 :
    hubcapFit theRedpart rf8 p8_1739l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1745_1, c8_1745_2, c8_1745_3, c8_1745_4, c8_1745_5, c8_1745_6, c8_1745_7, c8_1745_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1738l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1738l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1738l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1738l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1747_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1738l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1747 :
    hubcapFit theRedpart rf8 p8_1738l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1747_1, c8_1747_2, c8_1747_3, c8_1747_4, c8_1747_5, c8_1747_6, c8_1747_7, c8_1747_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1737l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1737l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1737l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1749_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1737l) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1749 :
    hubcapFit theRedpart rf8 p8_1737l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1749_1, c8_1749_2, c8_1749_3, c8_1749_4, c8_1749_5, c8_1749_6, c8_1749_7]

end FourColor

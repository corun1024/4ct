import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 31 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1682l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1682l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1682l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1682l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1682l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1689_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1682l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1689 :
    hubcapFit theRedpart rf7 p7_1682l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1689_1, c7_1689_2, c7_1689_3, c7_1689_4, c7_1689_5, c7_1689_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1691_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1681l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1691_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1681l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1691_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1681l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1691_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1681l) (hubSubn 7 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1691 :
    hubcapFit theRedpart rf7 p7_1681l
    (Hubcap.one 5 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 6 3 <|
     Hubcap.two 3 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1691_1, c7_1691_2, c7_1691_3, c7_1691_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1696_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1695r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1696_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1695r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1696_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1695r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1696_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1695r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1696_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1695r) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1696 :
    hubcapFit theRedpart rf7 p7_1695r
    (Hubcap.one 0 3 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1696_1, c7_1696_2, c7_1696_3, c7_1696_4, c7_1696_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1697_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1697_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1695l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1697_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1695l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1697_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1695l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1697_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1695l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1697 :
    hubcapFit theRedpart rf7 p7_1695l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1697_1, c7_1697_2, c7_1697_3, c7_1697_4, c7_1697_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1694l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1694l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1694l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1694l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1699_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1694l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1699 :
    hubcapFit theRedpart rf7 p7_1694l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1699_1, c7_1699_2, c7_1699_3, c7_1699_4, c7_1699_5, c7_1699_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1693l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1693l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1693l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1693l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1693l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1700_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1693l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1700 :
    hubcapFit theRedpart rf7 p7_1693l
    (Hubcap.one 0 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1700_1, c7_1700_2, c7_1700_3, c7_1700_4, c7_1700_5, c7_1700_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1702_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1692l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1702_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1692l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1702_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1692l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1702_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1692l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1702_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1692l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1702 :
    hubcapFit theRedpart rf7 p7_1692l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1702_1, c7_1702_2, c7_1702_3, c7_1702_4, c7_1702_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1704_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1704_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1679l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1704_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1679l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1704_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1679l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1704_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1679l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1704 :
    hubcapFit theRedpart rf7 p7_1679l
    (Hubcap.one 1 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1704_1, c7_1704_2, c7_1704_3, c7_1704_4, c7_1704_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1716r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1716r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1716r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1716r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1716r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1717_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1716r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1717 :
    hubcapFit theRedpart rf7 p7_1716r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1717_1, c7_1717_2, c7_1717_3, c7_1717_4, c7_1717_5, c7_1717_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1716l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1716l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1716l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1716l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1716l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1718_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1716l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1718 :
    hubcapFit theRedpart rf7 p7_1716l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1718_1, c7_1718_2, c7_1718_3, c7_1718_4, c7_1718_5, c7_1718_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1714l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1714l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1714l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1714l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1720_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1714l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1720 :
    hubcapFit theRedpart rf7 p7_1714l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1720_1, c7_1720_2, c7_1720_3, c7_1720_4, c7_1720_5, c7_1720_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1726_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1725r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1726_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1725r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1726_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1725r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1726_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1725r) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1726_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1725r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1726 :
    hubcapFit theRedpart rf7 p7_1725r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1726_1, c7_1726_2, c7_1726_3, c7_1726_4, c7_1726_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1725l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1725l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1725l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1725l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1725l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1727_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1725l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1727 :
    hubcapFit theRedpart rf7 p7_1725l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1727_1, c7_1727_2, c7_1727_3, c7_1727_4, c7_1727_5, c7_1727_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1724l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1724l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1724l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1724l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1724l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1729_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1724l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1729 :
    hubcapFit theRedpart rf7 p7_1724l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1729_1, c7_1729_2, c7_1729_3, c7_1729_4, c7_1729_5, c7_1729_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1722l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1722l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1722l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1722l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1722l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1731_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1722l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1731 :
    hubcapFit theRedpart rf7 p7_1722l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1731_1, c7_1731_2, c7_1731_3, c7_1731_4, c7_1731_5, c7_1731_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1712l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1712l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1712l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1712l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1733_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1712l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1733 :
    hubcapFit theRedpart rf7 p7_1712l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1733_1, c7_1733_2, c7_1733_3, c7_1733_4, c7_1733_5, c7_1733_6, c7_1733_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1736r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1736r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1736r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1736r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1736r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1736r) (hubSubn 7 6 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1737_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1736r) (hubSubn 7 6 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1737 :
    hubcapFit theRedpart rf7 p7_1736r
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 6 6 <|
     Hubcap.two 2 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1737_1, c7_1737_2, c7_1737_3, c7_1737_4, c7_1737_5, c7_1737_6, c7_1737_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1736l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1736l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1736l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1738_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1736l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1738 :
    hubcapFit theRedpart rf7 p7_1736l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1738_1, c7_1738_2, c7_1738_3, c7_1738_4, c7_1738_5, c7_1738_6, c7_1738_7]

end FourColor

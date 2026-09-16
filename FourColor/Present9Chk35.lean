import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 35 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1678r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1678r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1678r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1678r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1678r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1678r) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1679_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1678r) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1679 :
    hubcapFit theRedpart rf9 p9_1678r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1679_1, c9_1679_2, c9_1679_3, c9_1679_4, c9_1679_5, c9_1679_6, c9_1679_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1678l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1678l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1678l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1678l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1680_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1678l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1680 :
    hubcapFit theRedpart rf9 p9_1678l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1680_1, c9_1680_2, c9_1680_3, c9_1680_4, c9_1680_5, c9_1680_6, c9_1680_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1676l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1676l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1676l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1682_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1676l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1682 :
    hubcapFit theRedpart rf9 p9_1676l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1682_1, c9_1682_2, c9_1682_3, c9_1682_4, c9_1682_5, c9_1682_6, c9_1682_7, c9_1682_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1673l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1673l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1673l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1673l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1684_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1673l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1684 :
    hubcapFit theRedpart rf9 p9_1673l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1684_1, c9_1684_2, c9_1684_3, c9_1684_4, c9_1684_5, c9_1684_6, c9_1684_7, c9_1684_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1671l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1671l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1671l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1671l) (hubSubn 9 4 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1686_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1671l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1686 :
    hubcapFit theRedpart rf9 p9_1671l
    (Hubcap.one 0 3 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 4 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1686_1, c9_1686_2, c9_1686_3, c9_1686_4, c9_1686_5, c9_1686_6, c9_1686_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1669l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1669l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1669l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1669l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1688_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1669l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1688 :
    hubcapFit theRedpart rf9 p9_1669l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1688_1, c9_1688_2, c9_1688_3, c9_1688_4, c9_1688_5, c9_1688_6, c9_1688_7, c9_1688_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1668l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1668l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1668l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1668l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1690_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1668l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1690 :
    hubcapFit theRedpart rf9 p9_1668l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1690_1, c9_1690_2, c9_1690_3, c9_1690_4, c9_1690_5, c9_1690_6, c9_1690_7, c9_1690_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1667l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1667l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1667l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1692_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1667l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1692 :
    hubcapFit theRedpart rf9 p9_1667l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1692_1, c9_1692_2, c9_1692_3, c9_1692_4, c9_1692_5, c9_1692_6, c9_1692_7, c9_1692_8, c9_1692_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1666l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1666l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1666l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1666l) (hubSubn 9 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1694_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1666l) (hubSubn 9 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1694 :
    hubcapFit theRedpart rf9 p9_1666l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 3 7 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1694_1, c9_1694_2, c9_1694_3, c9_1694_4, c9_1694_5, c9_1694_6, c9_1694_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1665l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1665l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1665l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1696_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1665l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1696 :
    hubcapFit theRedpart rf9 p9_1665l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1696_1, c9_1696_2, c9_1696_3, c9_1696_4, c9_1696_5, c9_1696_6, c9_1696_7, c9_1696_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1662l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1662l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1662l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1662l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1662l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1698_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1662l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1698 :
    hubcapFit theRedpart rf9 p9_1662l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1698_1, c9_1698_2, c9_1698_3, c9_1698_4, c9_1698_5, c9_1698_6, c9_1698_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1661l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1661l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1661l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1700_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1661l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1700 :
    hubcapFit theRedpart rf9 p9_1661l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1700_1, c9_1700_2, c9_1700_3, c9_1700_4, c9_1700_5, c9_1700_6, c9_1700_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1660l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1660l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1660l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1702_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1660l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1702 :
    hubcapFit theRedpart rf9 p9_1660l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1702_1, c9_1702_2, c9_1702_3, c9_1702_4, c9_1702_5, c9_1702_6, c9_1702_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1659l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1659l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1659l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1659l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1659l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1704_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1659l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1704 :
    hubcapFit theRedpart rf9 p9_1659l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1704_1, c9_1704_2, c9_1704_3, c9_1704_4, c9_1704_5, c9_1704_6]

end FourColor

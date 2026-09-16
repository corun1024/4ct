import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 32 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1735l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1735l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1735l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1735l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1740_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1735l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1740 :
    hubcapFit theRedpart rf7 p7_1735l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1740_1, c7_1740_2, c7_1740_3, c7_1740_4, c7_1740_5, c7_1740_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1709l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1709l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1709l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1709l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1709l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1742_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1709l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1742 :
    hubcapFit theRedpart rf7 p7_1709l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1742_1, c7_1742_2, c7_1742_3, c7_1742_4, c7_1742_5, c7_1742_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1743_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1743_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1708l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1743_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1708l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1743_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1708l) (hubSubn 7 2 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1743_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1708l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1743 :
    hubcapFit theRedpart rf7 p7_1708l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 2 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1743_1, c7_1743_2, c7_1743_3, c7_1743_4, c7_1743_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1745_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1745_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1745_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1707l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1745_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1707l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1745_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1707l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1745 :
    hubcapFit theRedpart rf7 p7_1707l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1745_1, c7_1745_2, c7_1745_3, c7_1745_4, c7_1745_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1758r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1758r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1758r) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1758r) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1758r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1759_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1758r) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1759 :
    hubcapFit theRedpart rf7 p7_1758r
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1759_1, c7_1759_2, c7_1759_3, c7_1759_4, c7_1759_5, c7_1759_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1760_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1758l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1760_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1758l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1760_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1758l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1760_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1758l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1760 :
    hubcapFit theRedpart rf7 p7_1758l
    (Hubcap.one 3 (-1) <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1760_1, c7_1760_2, c7_1760_3, c7_1760_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1762_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1757l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1762_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1757l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1762_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1757l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1762_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1757l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1762_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1757l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1762 :
    hubcapFit theRedpart rf7 p7_1757l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1762_1, c7_1762_2, c7_1762_3, c7_1762_4, c7_1762_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1756l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1756l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1756l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1756l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1756l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1763_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1756l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1763 :
    hubcapFit theRedpart rf7 p7_1756l
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1763_1, c7_1763_2, c7_1763_3, c7_1763_4, c7_1763_5, c7_1763_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1755l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1755l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1755l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1755l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1755l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1765_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1755l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1765 :
    hubcapFit theRedpart rf7 p7_1755l
    (Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1765_1, c7_1765_2, c7_1765_3, c7_1765_4, c7_1765_5, c7_1765_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1770_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1769r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1770_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1769r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1770_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1769r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1770_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1769r) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1770_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1769r) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1770 :
    hubcapFit theRedpart rf7 p7_1769r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1770_1, c7_1770_2, c7_1770_3, c7_1770_4, c7_1770_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1771_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1769l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1771_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1769l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1771_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1769l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1771_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1769l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1771_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1769l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1771 :
    hubcapFit theRedpart rf7 p7_1769l
    (Hubcap.one 1 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1771_1, c7_1771_2, c7_1771_3, c7_1771_4, c7_1771_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1773_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1768l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1773_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1768l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1773_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1768l) (hubSubn 7 4 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1773_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1768l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1773 :
    hubcapFit theRedpart rf7 p7_1768l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1773_1, c7_1773_2, c7_1773_3, c7_1773_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1767l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1767l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1767l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1767l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1767l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1774_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1767l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1774 :
    hubcapFit theRedpart rf7 p7_1767l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1774_1, c7_1774_2, c7_1774_3, c7_1774_4, c7_1774_5, c7_1774_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1776_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1766l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1776_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1766l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1776_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1766l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1776_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1766l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1776_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1766l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1776 :
    hubcapFit theRedpart rf7 p7_1766l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1776_1, c7_1776_2, c7_1776_3, c7_1776_4, c7_1776_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1778_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1753l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1778_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1753l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1778_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1753l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1778_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1753l) (hubSubn 7 2 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1778_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1753l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1778 :
    hubcapFit theRedpart rf7 p7_1753l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 2 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1778_1, c7_1778_2, c7_1778_3, c7_1778_4, c7_1778_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1783_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1782r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1783_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1782r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1783_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1782r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1783_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1782r) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1783_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1782r) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1783 :
    hubcapFit theRedpart rf7 p7_1782r
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 2 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1783_1, c7_1783_2, c7_1783_3, c7_1783_4, c7_1783_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1782l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1782l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1782l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1782l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1782l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1784_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1782l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1784 :
    hubcapFit theRedpart rf7 p7_1782l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1784_1, c7_1784_2, c7_1784_3, c7_1784_4, c7_1784_5, c7_1784_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1786_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1781l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1786_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1781l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1786_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1781l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1786_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1781l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1786_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1781l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1786 :
    hubcapFit theRedpart rf7 p7_1781l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1786_1, c7_1786_2, c7_1786_3, c7_1786_4, c7_1786_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1787_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1787_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1787_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1787_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1780l) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1787_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1780l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1787 :
    hubcapFit theRedpart rf7 p7_1780l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1787_1, c7_1787_2, c7_1787_3, c7_1787_4, c7_1787_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1789_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1789_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1779l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1789_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1779l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1789_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1779l) (hubSubn 7 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1789_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1779l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1789 :
    hubcapFit theRedpart rf7 p7_1779l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1789_1, c7_1789_2, c7_1789_3, c7_1789_4, c7_1789_5]

end FourColor

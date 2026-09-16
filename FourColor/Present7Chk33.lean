import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 33 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1791_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1751l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1791_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1751l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1791_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1751l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1791_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1751l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1791 :
    hubcapFit theRedpart rf7 p7_1751l
    (Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1791_1, c7_1791_2, c7_1791_3, c7_1791_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1792_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1750l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1792_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1750l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1792_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1750l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1792_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1750l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1792_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1750l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1792 :
    hubcapFit theRedpart rf7 p7_1750l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1792_1, c7_1792_2, c7_1792_3, c7_1792_4, c7_1792_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1749l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1749l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1749l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1749l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1794_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1749l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1794 :
    hubcapFit theRedpart rf7 p7_1749l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1794_1, c7_1794_2, c7_1794_3, c7_1794_4, c7_1794_5, c7_1794_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1795_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1748l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1795_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1748l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1795_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1748l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1795_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1748l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1795_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1748l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1795 :
    hubcapFit theRedpart rf7 p7_1748l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1795_1, c7_1795_2, c7_1795_3, c7_1795_4, c7_1795_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1747l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1747l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1747l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1747l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1747l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1797_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1747l) (hubSubn 7 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1797 :
    hubcapFit theRedpart rf7 p7_1747l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1797_1, c7_1797_2, c7_1797_3, c7_1797_4, c7_1797_5, c7_1797_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1805r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1805r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1805r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1805r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1805r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1805r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1806_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1805r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1806 :
    hubcapFit theRedpart rf7 p7_1805r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1806_1, c7_1806_2, c7_1806_3, c7_1806_4, c7_1806_5, c7_1806_6, c7_1806_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1807_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1805l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1807_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1805l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1807_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1805l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1807_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1805l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1807_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1805l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1807 :
    hubcapFit theRedpart rf7 p7_1805l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1807_1, c7_1807_2, c7_1807_3, c7_1807_4, c7_1807_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1809_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1809_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1804l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1809_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1804l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1809_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1804l) (hubSubn 7 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1809_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1804l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1809 :
    hubcapFit theRedpart rf7 p7_1804l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1809_1, c7_1809_2, c7_1809_3, c7_1809_4, c7_1809_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1810_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1803l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1810_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1803l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1810_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1803l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1810_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1803l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1810_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1803l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1810 :
    hubcapFit theRedpart rf7 p7_1803l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1810_1, c7_1810_2, c7_1810_3, c7_1810_4, c7_1810_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1812_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1802l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1812_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1802l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1812_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1802l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1812_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1802l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1812_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1802l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1812 :
    hubcapFit theRedpart rf7 p7_1802l
    (Hubcap.one 0 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1812_1, c7_1812_2, c7_1812_3, c7_1812_4, c7_1812_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1801l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1801l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1801l) (hubSubn 7 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1801l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1813_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1801l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1813 :
    hubcapFit theRedpart rf7 p7_1801l
    (Hubcap.one 0 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 2 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1813_1, c7_1813_2, c7_1813_3, c7_1813_4, c7_1813_5, c7_1813_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1800l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1800l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1800l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1815_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1800l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1815 :
    hubcapFit theRedpart rf7 p7_1800l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1815_1, c7_1815_2, c7_1815_3, c7_1815_4, c7_1815_5, c7_1815_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1816_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1799l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1816_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1799l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1816_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1799l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1816_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1799l) (hubSubn 7 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1816_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1799l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1816 :
    hubcapFit theRedpart rf7 p7_1799l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1816_1, c7_1816_2, c7_1816_3, c7_1816_4, c7_1816_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1846r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1846r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1846r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1846r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1846r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1846r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1847_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1846r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1847 :
    hubcapFit theRedpart rf7 p7_1846r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1847_1, c7_1847_2, c7_1847_3, c7_1847_4, c7_1847_5, c7_1847_6, c7_1847_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1846l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1846l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1846l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1848_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1846l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1848 :
    hubcapFit theRedpart rf7 p7_1846l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1848_1, c7_1848_2, c7_1848_3, c7_1848_4, c7_1848_5, c7_1848_6, c7_1848_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1845l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1845l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1850_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1845l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1850 :
    hubcapFit theRedpart rf7 p7_1845l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1850_1, c7_1850_2, c7_1850_3, c7_1850_4, c7_1850_5, c7_1850_6, c7_1850_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1842l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1842l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1842l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1842l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1852_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1842l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1852 :
    hubcapFit theRedpart rf7 p7_1842l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1852_1, c7_1852_2, c7_1852_3, c7_1852_4, c7_1852_5, c7_1852_6, c7_1852_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_1841l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_1841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_1841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_1841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_1841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_1841l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_1854_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_1841l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_1854 :
    hubcapFit theRedpart rf7 p7_1841l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_1854_1, c7_1854_2, c7_1854_3, c7_1854_4, c7_1854_5, c7_1854_6, c7_1854_7]

end FourColor

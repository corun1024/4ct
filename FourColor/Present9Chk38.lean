import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 38 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1775l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1775l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1775l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1775l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1786_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1775l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1786 :
    hubcapFit theRedpart rf9 p9_1775l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1786_1, c9_1786_2, c9_1786_3, c9_1786_4, c9_1786_5, c9_1786_6, c9_1786_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1801r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1801r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1801r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1801r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1801r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1801r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1801r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1801r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1802_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1801r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1802 :
    hubcapFit theRedpart rf9 p9_1801r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1802_1, c9_1802_2, c9_1802_3, c9_1802_4, c9_1802_5, c9_1802_6, c9_1802_7, c9_1802_8, c9_1802_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1801l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1801l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1801l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1803_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1801l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1803 :
    hubcapFit theRedpart rf9 p9_1801l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1803_1, c9_1803_2, c9_1803_3, c9_1803_4, c9_1803_5, c9_1803_6, c9_1803_7, c9_1803_8, c9_1803_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1799l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1799l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1799l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1799l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1799l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1805_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1799l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1805 :
    hubcapFit theRedpart rf9 p9_1799l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1805_1, c9_1805_2, c9_1805_3, c9_1805_4, c9_1805_5, c9_1805_6, c9_1805_7, c9_1805_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1797l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1797l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1797l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1797l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1797l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1797l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1797l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1807_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1797l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1807 :
    hubcapFit theRedpart rf9 p9_1797l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1807_1, c9_1807_2, c9_1807_3, c9_1807_4, c9_1807_5, c9_1807_6, c9_1807_7, c9_1807_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1796l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1796l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1796l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1796l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1796l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1796l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1809_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1796l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1809 :
    hubcapFit theRedpart rf9 p9_1796l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1809_1, c9_1809_2, c9_1809_3, c9_1809_4, c9_1809_5, c9_1809_6, c9_1809_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1794l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1794l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1794l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1794l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1811_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1794l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1811 :
    hubcapFit theRedpart rf9 p9_1794l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1811_1, c9_1811_2, c9_1811_3, c9_1811_4, c9_1811_5, c9_1811_6, c9_1811_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1793l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1793l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1793l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1793l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1793l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1793l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1813_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1793l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1813 :
    hubcapFit theRedpart rf9 p9_1793l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1813_1, c9_1813_2, c9_1813_3, c9_1813_4, c9_1813_5, c9_1813_6, c9_1813_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1792l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1792l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1792l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1792l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1792l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1792l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1815_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1792l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1815 :
    hubcapFit theRedpart rf9 p9_1792l
    (Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1815_1, c9_1815_2, c9_1815_3, c9_1815_4, c9_1815_5, c9_1815_6, c9_1815_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1791l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1791l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1791l) (hubSubn 9 5 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1791l) (hubSubn 9 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1791l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1791l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1817_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1791l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1817 :
    hubcapFit theRedpart rf9 p9_1791l
    (Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 5 8 <|
     Hubcap.two 4 6 6 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1817_1, c9_1817_2, c9_1817_3, c9_1817_4, c9_1817_5, c9_1817_6, c9_1817_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_1 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1820r) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_2 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1820r) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1820r) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1820r) (hubSubn 9 8 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1820r) (hubSubn 9 7 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1820r) (hubSubn 9 8 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1821_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1820r) (hubSubn 9 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1821 :
    hubcapFit theRedpart rf9 p9_1820r
    (Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 6 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 2 8 7 <|
     Hubcap.two 3 7 8 <|
     Hubcap.two 3 8 8 <|
     Hubcap.two 4 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1821_1, c9_1821_2, c9_1821_3, c9_1821_4, c9_1821_5, c9_1821_6, c9_1821_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1820l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1820l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1820l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1820l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1820l) (hubSubn 9 8 3) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1822_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1820l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1822 :
    hubcapFit theRedpart rf9 p9_1820l
    (Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 8 8 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1822_1, c9_1822_2, c9_1822_3, c9_1822_4, c9_1822_5, c9_1822_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1819l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1819l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1819l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1819l) (hubSubn 9 7 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1824_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1819l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1824 :
    hubcapFit theRedpart rf9 p9_1819l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 7 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1824_1, c9_1824_2, c9_1824_3, c9_1824_4, c9_1824_5, c9_1824_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1826l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1826l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1826l) (hubSubn 9 4 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1826l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1827_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1826l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1827 :
    hubcapFit theRedpart rf9 p9_1826l
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1827_1, c9_1827_2, c9_1827_3, c9_1827_4, c9_1827_5, c9_1827_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1829l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1829l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1829l) (hubSubn 9 4 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1829l) (hubSubn 9 3 1) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1830_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1829l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1830 :
    hubcapFit theRedpart rf9 p9_1829l
    (Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 4 8 <|
     Hubcap.two 1 3 8 <|
     Hubcap.two 2 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1830_1, c9_1830_2, c9_1830_3, c9_1830_4, c9_1830_5, c9_1830_6]

end FourColor

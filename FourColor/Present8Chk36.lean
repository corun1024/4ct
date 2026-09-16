import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 36 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1796_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1795l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1796_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1795l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1796_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1795l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1796_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1795l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1796_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1795l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1796 :
    hubcapFit theRedpart rf8 p8_1795l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1796_1, c8_1796_2, c8_1796_3, c8_1796_4, c8_1796_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1799_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1798l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1799_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1798l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1799_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1798l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1799_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1798l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1799_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1798l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1799 :
    hubcapFit theRedpart rf8 p8_1798l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1799_1, c8_1799_2, c8_1799_3, c8_1799_4, c8_1799_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1803_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1802l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1803_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1802l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1803_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1802l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1803_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1802l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1803_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1802l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1803 :
    hubcapFit theRedpart rf8 p8_1802l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1803_1, c8_1803_2, c8_1803_3, c8_1803_4, c8_1803_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1805_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1802r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1805_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1802r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1805_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1802r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1805_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1802r) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1805_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1802r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1805 :
    hubcapFit theRedpart rf8 p8_1802r
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1805_1, c8_1805_2, c8_1805_3, c8_1805_4, c8_1805_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1808_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1801r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1808_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1801r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1808_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1801r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1808_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1801r) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1808_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1801r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1808 :
    hubcapFit theRedpart rf8 p8_1801r
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1808_1, c8_1808_2, c8_1808_3, c8_1808_4, c8_1808_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1820r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1820r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1820r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1820r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1820r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1820r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1821_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1820r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1821 :
    hubcapFit theRedpart rf8 p8_1820r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1821_1, c8_1821_2, c8_1821_3, c8_1821_4, c8_1821_5, c8_1821_6, c8_1821_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1823l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1823l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1824_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1823l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1824 :
    hubcapFit theRedpart rf8 p8_1823l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1824_1, c8_1824_2, c8_1824_3, c8_1824_4, c8_1824_5, c8_1824_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1823r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1823r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1823r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1823r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1823r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1826_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1823r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1826 :
    hubcapFit theRedpart rf8 p8_1823r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1826_1, c8_1826_2, c8_1826_3, c8_1826_4, c8_1826_5, c8_1826_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1829l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1829l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1830_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1829l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1830 :
    hubcapFit theRedpart rf8 p8_1829l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1830_1, c8_1830_2, c8_1830_3, c8_1830_4, c8_1830_5, c8_1830_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1829r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1829r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1832_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1829r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1832 :
    hubcapFit theRedpart rf8 p8_1829r
    (Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1832_1, c8_1832_2, c8_1832_3, c8_1832_4, c8_1832_5, c8_1832_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1819l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1819l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1819l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1819l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1819l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1819l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1837_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1819l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1837 :
    hubcapFit theRedpart rf8 p8_1819l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1837_1, c8_1837_2, c8_1837_3, c8_1837_4, c8_1837_5, c8_1837_6, c8_1837_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1839l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1839l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1839l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1839l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1840_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1839l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1840 :
    hubcapFit theRedpart rf8 p8_1839l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1840_1, c8_1840_2, c8_1840_3, c8_1840_4, c8_1840_5, c8_1840_6, c8_1840_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1843l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1843l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1843l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1843l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1843l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1844_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1843l) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1844 :
    hubcapFit theRedpart rf8 p8_1843l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1844_1, c8_1844_2, c8_1844_3, c8_1844_4, c8_1844_5, c8_1844_6, c8_1844_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1843r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1843r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1843r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1843r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1843r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1843r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1846_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1843r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1846 :
    hubcapFit theRedpart rf8 p8_1843r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1846_1, c8_1846_2, c8_1846_3, c8_1846_4, c8_1846_5, c8_1846_6, c8_1846_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1842r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1842r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1842r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1842r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1842r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1842r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1849_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1842r) (hubSubn 8 6 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1849 :
    hubcapFit theRedpart rf8 p8_1842r
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1849_1, c8_1849_2, c8_1849_3, c8_1849_4, c8_1849_5, c8_1849_6, c8_1849_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1817l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1817l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1817l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1817l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1817l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1817l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1853_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1817l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1853 :
    hubcapFit theRedpart rf8 p8_1817l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 2 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1853_1, c8_1853_2, c8_1853_3, c8_1853_4, c8_1853_5, c8_1853_6, c8_1853_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1855l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1855l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1855l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1855l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1855l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1856_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1855l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1856 :
    hubcapFit theRedpart rf8 p8_1855l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 3 7 5 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1856_1, c8_1856_2, c8_1856_3, c8_1856_4, c8_1856_5, c8_1856_6]

end FourColor

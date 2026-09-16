import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 35 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1736l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1736l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1751_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1736l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1751 :
    hubcapFit theRedpart rf8 p8_1736l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1751_1, c8_1751_2, c8_1751_3, c8_1751_4, c8_1751_5, c8_1751_6, c8_1751_7, c8_1751_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1735l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1735l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1735l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1735l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1753_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1735l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1753 :
    hubcapFit theRedpart rf8 p8_1735l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1753_1, c8_1753_2, c8_1753_3, c8_1753_4, c8_1753_5, c8_1753_6, c8_1753_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1734l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1734l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1734l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1734l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1755_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1734l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1755 :
    hubcapFit theRedpart rf8 p8_1734l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1755_1, c8_1755_2, c8_1755_3, c8_1755_4, c8_1755_5, c8_1755_6, c8_1755_7, c8_1755_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1733l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1733l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1733l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1733l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1757_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1733l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1757 :
    hubcapFit theRedpart rf8 p8_1733l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1757_1, c8_1757_2, c8_1757_3, c8_1757_4, c8_1757_5, c8_1757_6, c8_1757_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1759r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1759r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1759r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1759r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1759r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1759r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1760_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1759r) (hubSubn 8 2 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1760 :
    hubcapFit theRedpart rf8 p8_1759r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 1 2 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1760_1, c8_1760_2, c8_1760_3, c8_1760_4, c8_1760_5, c8_1760_6, c8_1760_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1759l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1759l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1759l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1759l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1759l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1759l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1761_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1759l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1761 :
    hubcapFit theRedpart rf8 p8_1759l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 1 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1761_1, c8_1761_2, c8_1761_3, c8_1761_4, c8_1761_5, c8_1761_6, c8_1761_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1730l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1730l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1730l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_1730l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1730l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1763_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1730l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1763 :
    hubcapFit theRedpart rf8 p8_1730l
    (Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 2 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1763_1, c8_1763_2, c8_1763_3, c8_1763_4, c8_1763_5, c8_1763_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1765l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1765l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1765l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1765l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1765l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1766_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1765l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1766 :
    hubcapFit theRedpart rf8 p8_1765l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1766_1, c8_1766_2, c8_1766_3, c8_1766_4, c8_1766_5, c8_1766_6, c8_1766_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1765r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_1765r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1765r) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1765r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1765r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1768_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1765r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1768 :
    hubcapFit theRedpart rf8 p8_1765r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1768_1, c8_1768_2, c8_1768_3, c8_1768_4, c8_1768_5, c8_1768_6, c8_1768_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1771_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1727l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1771_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1727l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1771_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1727l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1771_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1727l) (hubSubn 8 7 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1771_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1727l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1771 :
    hubcapFit theRedpart rf8 p8_1727l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1771_1, c8_1771_2, c8_1771_3, c8_1771_4, c8_1771_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1725l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1725l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1725l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1725l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1725l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1773_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1725l) (hubSubn 8 7 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1773 :
    hubcapFit theRedpart rf8 p8_1725l
    (Hubcap.one 4 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1773_1, c8_1773_2, c8_1773_3, c8_1773_4, c8_1773_5, c8_1773_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1724l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_1724l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1724l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1724l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1724l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1775_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1724l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1775 :
    hubcapFit theRedpart rf8 p8_1724l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1775_1, c8_1775_2, c8_1775_3, c8_1775_4, c8_1775_5, c8_1775_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1778_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1777l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1778_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1777l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1778_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1777l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1778_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1777l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1778_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1777l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1778 :
    hubcapFit theRedpart rf8 p8_1777l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1778_1, c8_1778_2, c8_1778_3, c8_1778_4, c8_1778_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1781_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1780l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1781_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1780l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1781_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1780l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1781_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1780l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1781_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1780l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1781 :
    hubcapFit theRedpart rf8 p8_1780l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1781_1, c8_1781_2, c8_1781_3, c8_1781_4, c8_1781_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1785_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1784l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1785_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1784l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1785_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1784l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1785_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1784l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1785_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1784l) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1785 :
    hubcapFit theRedpart rf8 p8_1784l
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1785_1, c8_1785_2, c8_1785_3, c8_1785_4, c8_1785_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1787_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1784r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1787_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1784r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1787_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1784r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1787_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1784r) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1787_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1784r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1787 :
    hubcapFit theRedpart rf8 p8_1784r
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1787_1, c8_1787_2, c8_1787_3, c8_1787_4, c8_1787_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1790_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_1783r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1790_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_1783r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1790_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_1783r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1790_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_1783r) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_1790_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_1783r) (hubSubn 8 6 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_1790 :
    hubcapFit theRedpart rf8 p8_1783r
    (Hubcap.one 2 0 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 3 7 6 <|
     Hubcap.two 4 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_1790_1, c8_1790_2, c8_1790_3, c8_1790_4, c8_1790_5]

end FourColor

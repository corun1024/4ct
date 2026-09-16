import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 37 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1545l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1545l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1545l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1744_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1545l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1744 :
    hubcapFit theRedpart rf9 p9_1545l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1744_1, c9_1744_2, c9_1744_3, c9_1744_4, c9_1744_5, c9_1744_6, c9_1744_7, c9_1744_8, c9_1744_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1544l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1544l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1544l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1746_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1544l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1746 :
    hubcapFit theRedpart rf9 p9_1544l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1746_1, c9_1746_2, c9_1746_3, c9_1746_4, c9_1746_5, c9_1746_6, c9_1746_7, c9_1746_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1543l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1543l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1543l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1748_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1543l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1748 :
    hubcapFit theRedpart rf9 p9_1543l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1748_1, c9_1748_2, c9_1748_3, c9_1748_4, c9_1748_5, c9_1748_6, c9_1748_7, c9_1748_8, c9_1748_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1542l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1542l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1542l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1542l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1750_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1542l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1750 :
    hubcapFit theRedpart rf9 p9_1542l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1750_1, c9_1750_2, c9_1750_3, c9_1750_4, c9_1750_5, c9_1750_6, c9_1750_7, c9_1750_8, c9_1750_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1541l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1541l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1541l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1541l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1752_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1541l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1752 :
    hubcapFit theRedpart rf9 p9_1541l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 5 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1752_1, c9_1752_2, c9_1752_3, c9_1752_4, c9_1752_5, c9_1752_6, c9_1752_7, c9_1752_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1765r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1765r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1765r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1765r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1765r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1765r) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1766_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1765r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1766 :
    hubcapFit theRedpart rf9 p9_1765r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1766_1, c9_1766_2, c9_1766_3, c9_1766_4, c9_1766_5, c9_1766_6, c9_1766_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1765l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1765l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1765l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1767_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1765l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1767 :
    hubcapFit theRedpart rf9 p9_1765l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1767_1, c9_1767_2, c9_1767_3, c9_1767_4, c9_1767_5, c9_1767_6, c9_1767_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1764l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1764l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1764l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1769_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1764l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1769 :
    hubcapFit theRedpart rf9 p9_1764l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1769_1, c9_1769_2, c9_1769_3, c9_1769_4, c9_1769_5, c9_1769_6, c9_1769_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1763l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1763l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1763l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1763l) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1771_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1763l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1771 :
    hubcapFit theRedpart rf9 p9_1763l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1771_1, c9_1771_2, c9_1771_3, c9_1771_4, c9_1771_5, c9_1771_6, c9_1771_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1762l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1762l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1762l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1762l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1762l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1762l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1773_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1762l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1773 :
    hubcapFit theRedpart rf9 p9_1762l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1773_1, c9_1773_2, c9_1773_3, c9_1773_4, c9_1773_5, c9_1773_6, c9_1773_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1778r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1778r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1778r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1778r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1778r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1778r) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1779_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1778r) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1779 :
    hubcapFit theRedpart rf9 p9_1778r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1779_1, c9_1779_2, c9_1779_3, c9_1779_4, c9_1779_5, c9_1779_6, c9_1779_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1778l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1778l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1778l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1778l) (hubSubn 9 1 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1780_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1778l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1780 :
    hubcapFit theRedpart rf9 p9_1778l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 8 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1780_1, c9_1780_2, c9_1780_3, c9_1780_4, c9_1780_5, c9_1780_6, c9_1780_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1777l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1777l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1777l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1777l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1777l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1777l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1777l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1782_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1777l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1782 :
    hubcapFit theRedpart rf9 p9_1777l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1782_1, c9_1782_2, c9_1782_3, c9_1782_4, c9_1782_5, c9_1782_6, c9_1782_7, c9_1782_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1776l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1776l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1776l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1776l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1776l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1776l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1784_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1776l) (hubSubn 9 6 5) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1784 :
    hubcapFit theRedpart rf9 p9_1776l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1784_1, c9_1784_2, c9_1784_3, c9_1784_4, c9_1784_5, c9_1784_6, c9_1784_7, c9_1784_8]

end FourColor

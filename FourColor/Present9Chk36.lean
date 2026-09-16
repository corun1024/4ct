import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 36 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1715r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1715r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1715r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1715r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1715r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1715r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1716_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1715r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1716 :
    hubcapFit theRedpart rf9 p9_1715r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1716_1, c9_1716_2, c9_1716_3, c9_1716_4, c9_1716_5, c9_1716_6, c9_1716_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1715l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1715l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1715l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1715l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1717_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1715l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1717 :
    hubcapFit theRedpart rf9 p9_1715l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1717_1, c9_1717_2, c9_1717_3, c9_1717_4, c9_1717_5, c9_1717_6, c9_1717_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1714l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1714l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1714l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1714l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1719_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1714l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1719 :
    hubcapFit theRedpart rf9 p9_1714l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1719_1, c9_1719_2, c9_1719_3, c9_1719_4, c9_1719_5, c9_1719_6, c9_1719_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1713l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1713l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1713l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1713l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1713l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1721_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1713l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1721 :
    hubcapFit theRedpart rf9 p9_1713l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1721_1, c9_1721_2, c9_1721_3, c9_1721_4, c9_1721_5, c9_1721_6, c9_1721_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1712l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1712l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1712l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1712l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1712l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1723_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1712l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1723 :
    hubcapFit theRedpart rf9 p9_1712l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1723_1, c9_1723_2, c9_1723_3, c9_1723_4, c9_1723_5, c9_1723_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1711l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1711l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1711l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1711l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1711l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1711l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1711l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1724_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1711l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1724 :
    hubcapFit theRedpart rf9 p9_1711l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1724_1, c9_1724_2, c9_1724_3, c9_1724_4, c9_1724_5, c9_1724_6, c9_1724_7, c9_1724_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1710l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1710l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1710l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1710l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1710l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1710l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1726_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1710l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1726 :
    hubcapFit theRedpart rf9 p9_1710l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1726_1, c9_1726_2, c9_1726_3, c9_1726_4, c9_1726_5, c9_1726_6, c9_1726_7, c9_1726_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1709l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1709l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1709l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1709l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1709l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1728_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1709l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1728 :
    hubcapFit theRedpart rf9 p9_1709l
    (Hubcap.one 4 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1728_1, c9_1728_2, c9_1728_3, c9_1728_4, c9_1728_5, c9_1728_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1708l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1708l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1708l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1708l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1729_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1708l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1729 :
    hubcapFit theRedpart rf9 p9_1708l
    (Hubcap.one 2 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1729_1, c9_1729_2, c9_1729_3, c9_1729_4, c9_1729_5, c9_1729_6, c9_1729_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1707l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1707l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1707l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1731_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1707l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1731 :
    hubcapFit theRedpart rf9 p9_1707l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1731_1, c9_1731_2, c9_1731_3, c9_1731_4, c9_1731_5, c9_1731_6, c9_1731_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1706l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1706l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1706l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1733_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1706l) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1733 :
    hubcapFit theRedpart rf9 p9_1706l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1733_1, c9_1733_2, c9_1733_3, c9_1733_4, c9_1733_5, c9_1733_6, c9_1733_7, c9_1733_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1705l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1705l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1705l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1735_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1705l) (hubSubn 9 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1735 :
    hubcapFit theRedpart rf9 p9_1705l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1735_1, c9_1735_2, c9_1735_3, c9_1735_4, c9_1735_5, c9_1735_6, c9_1735_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1657l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1657l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1738_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1657l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1738 :
    hubcapFit theRedpart rf9 p9_1657l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1738_1, c9_1738_2, c9_1738_3, c9_1738_4, c9_1738_5, c9_1738_6, c9_1738_7, c9_1738_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1656l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1656l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1656l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1740_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1656l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1740 :
    hubcapFit theRedpart rf9 p9_1656l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1740_1, c9_1740_2, c9_1740_3, c9_1740_4, c9_1740_5, c9_1740_6, c9_1740_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1546l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1546l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1742_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1546l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1742 :
    hubcapFit theRedpart rf9 p9_1546l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1742_1, c9_1742_2, c9_1742_3, c9_1742_4, c9_1742_5, c9_1742_6, c9_1742_7, c9_1742_8]

end FourColor

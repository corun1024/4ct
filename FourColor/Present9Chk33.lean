import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 33 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1572r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1572r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1572r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1572r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1572r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1572r) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1573_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1572r) (hubSubn 9 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1573 :
    hubcapFit theRedpart rf9 p9_1572r
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1573_1, c9_1573_2, c9_1573_3, c9_1573_4, c9_1573_5, c9_1573_6, c9_1573_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1572l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1572l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1572l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1574_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1572l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1574 :
    hubcapFit theRedpart rf9 p9_1572l
    (Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1574_1, c9_1574_2, c9_1574_3, c9_1574_4, c9_1574_5, c9_1574_6, c9_1574_7, c9_1574_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1570l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1570l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1570l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1570l) (hubSubn 9 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1576_9 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1570l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1576 :
    hubcapFit theRedpart rf9 p9_1570l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1576_1, c9_1576_2, c9_1576_3, c9_1576_4, c9_1576_5, c9_1576_6, c9_1576_7, c9_1576_8, c9_1576_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1569l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1569l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1578_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1569l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1578 :
    hubcapFit theRedpart rf9 p9_1569l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1578_1, c9_1578_2, c9_1578_3, c9_1578_4, c9_1578_5, c9_1578_6, c9_1578_7, c9_1578_8, c9_1578_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1568l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1568l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1580_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1580 :
    hubcapFit theRedpart rf9 p9_1568l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1580_1, c9_1580_2, c9_1580_3, c9_1580_4, c9_1580_5, c9_1580_6, c9_1580_7, c9_1580_8, c9_1580_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1584r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1584r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1584r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1584r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1584r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1584r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1584r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1585_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1584r) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1585 :
    hubcapFit theRedpart rf9 p9_1584r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1585_1, c9_1585_2, c9_1585_3, c9_1585_4, c9_1585_5, c9_1585_6, c9_1585_7, c9_1585_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1584l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1584l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1584l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1584l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1586_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1584l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1586 :
    hubcapFit theRedpart rf9 p9_1584l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1586_1, c9_1586_2, c9_1586_3, c9_1586_4, c9_1586_5, c9_1586_6, c9_1586_7, c9_1586_8, c9_1586_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1565l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1589_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1565l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1589 :
    hubcapFit theRedpart rf9 p9_1565l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1589_1, c9_1589_2, c9_1589_3, c9_1589_4, c9_1589_5, c9_1589_6, c9_1589_7, c9_1589_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1564l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1564l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1591_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1591 :
    hubcapFit theRedpart rf9 p9_1564l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1591_1, c9_1591_2, c9_1591_3, c9_1591_4, c9_1591_5, c9_1591_6, c9_1591_7, c9_1591_8, c9_1591_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1562l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1593_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1562l) (hubSubn 9 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1593 :
    hubcapFit theRedpart rf9 p9_1562l
    (Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1593_1, c9_1593_2, c9_1593_3, c9_1593_4, c9_1593_5, c9_1593_6, c9_1593_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1555l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1555l) (hubSubn 9 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1555l) (hubSubn 9 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1596_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1555l) (hubSubn 9 6 4) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1596 :
    hubcapFit theRedpart rf9 p9_1555l
    (Hubcap.one 5 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1596_1, c9_1596_2, c9_1596_3, c9_1596_4, c9_1596_5, c9_1596_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1608r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1608r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1609_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1608r) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1609 :
    hubcapFit theRedpart rf9 p9_1608r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1609_1, c9_1609_2, c9_1609_3, c9_1609_4, c9_1609_5, c9_1609_6, c9_1609_7, c9_1609_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1603l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1612_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1603l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1612 :
    hubcapFit theRedpart rf9 p9_1603l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1612_1, c9_1612_2, c9_1612_3, c9_1612_4, c9_1612_5, c9_1612_6, c9_1612_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1602l) (hubSubn 9 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1602l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1614_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1602l) (hubSubn 9 6 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1614 :
    hubcapFit theRedpart rf9 p9_1602l
    (Hubcap.one 0 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.two 5 6 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1614_1, c9_1614_2, c9_1614_3, c9_1614_4, c9_1614_5, c9_1614_6]

end FourColor

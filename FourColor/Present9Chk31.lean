import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 31 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1449l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1449l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1449l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1449l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1449l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1459_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1449l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1459 :
    hubcapFit theRedpart rf9 p9_1449l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1459_1, c9_1459_2, c9_1459_3, c9_1459_4, c9_1459_5, c9_1459_6, c9_1459_7, c9_1459_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1465r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1465r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1465r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1465r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1465r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1465r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1465r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1466_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1465r) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1466 :
    hubcapFit theRedpart rf9 p9_1465r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1466_1, c9_1466_2, c9_1466_3, c9_1466_4, c9_1466_5, c9_1466_6, c9_1466_7, c9_1466_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1465l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1465l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1465l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1465l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1465l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1465l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1465l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1467_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1465l) (hubSubn 9 4 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1467 :
    hubcapFit theRedpart rf9 p9_1465l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1467_1, c9_1467_2, c9_1467_3, c9_1467_4, c9_1467_5, c9_1467_6, c9_1467_7, c9_1467_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1463l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1463l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1463l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1463l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1463l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1469_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1463l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1469 :
    hubcapFit theRedpart rf9 p9_1463l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1469_1, c9_1469_2, c9_1469_3, c9_1469_4, c9_1469_5, c9_1469_6, c9_1469_7, c9_1469_8, c9_1469_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1461l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1461l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1471_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1461l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1471 :
    hubcapFit theRedpart rf9 p9_1461l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1471_1, c9_1471_2, c9_1471_3, c9_1471_4, c9_1471_5, c9_1471_6, c9_1471_7, c9_1471_8, c9_1471_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1445l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1445l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1445l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1473_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1445l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1473 :
    hubcapFit theRedpart rf9 p9_1445l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1473_1, c9_1473_2, c9_1473_3, c9_1473_4, c9_1473_5, c9_1473_6, c9_1473_7, c9_1473_8, c9_1473_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1444l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1444l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1444l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1475_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1444l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1475 :
    hubcapFit theRedpart rf9 p9_1444l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1475_1, c9_1475_2, c9_1475_3, c9_1475_4, c9_1475_5, c9_1475_6, c9_1475_7, c9_1475_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1443l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1443l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1443l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1477_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1443l) (hubSubn 9 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1477 :
    hubcapFit theRedpart rf9 p9_1443l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1477_1, c9_1477_2, c9_1477_3, c9_1477_4, c9_1477_5, c9_1477_6, c9_1477_7, c9_1477_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1442l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_1442l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1442l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1479_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1442l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1479 :
    hubcapFit theRedpart rf9 p9_1442l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1479_1, c9_1479_2, c9_1479_3, c9_1479_4, c9_1479_5, c9_1479_6, c9_1479_7, c9_1479_8, c9_1479_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1491r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1491r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1491r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1491r) (hubSubn 9 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1492_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1491r) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1492 :
    hubcapFit theRedpart rf9 p9_1491r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1492_1, c9_1492_2, c9_1492_3, c9_1492_4, c9_1492_5, c9_1492_6, c9_1492_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1491l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1491l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1491l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1491l) (hubSubn 9 4 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1493_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1491l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1493 :
    hubcapFit theRedpart rf9 p9_1491l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1493_1, c9_1493_2, c9_1493_3, c9_1493_4, c9_1493_5, c9_1493_6, c9_1493_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_1489l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1489l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1495_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1489l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1495 :
    hubcapFit theRedpart rf9 p9_1489l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1495_1, c9_1495_2, c9_1495_3, c9_1495_4, c9_1495_5, c9_1495_6, c9_1495_7, c9_1495_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1488l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1488l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1488l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_1488l) (hubSubn 9 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1497_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1488l) (hubSubn 9 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1497 :
    hubcapFit theRedpart rf9 p9_1488l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1497_1, c9_1497_2, c9_1497_3, c9_1497_4, c9_1497_5, c9_1497_6, c9_1497_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_1487l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_1487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_1487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_1487l) (hubSubn 9 3 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_1487l) (hubSubn 9 4 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_1499_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_1487l) (hubSubn 9 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_1499 :
    hubcapFit theRedpart rf9 p9_1487l
    (Hubcap.one 0 5 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 3 6 <|
     Hubcap.two 2 4 7 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_1499_1, c9_1499_2, c9_1499_3, c9_1499_4, c9_1499_5, c9_1499_6]

end FourColor

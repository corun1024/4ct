import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 13 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_582l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_582l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_582l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_582l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_582l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_582l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_582l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_584_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_582l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_584 :
    hubcapFit theRedpart rf9 p9_582l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_584_1, c9_584_2, c9_584_3, c9_584_4, c9_584_5, c9_584_6, c9_584_7, c9_584_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_581l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_581l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_581l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_586_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_581l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_586 :
    hubcapFit theRedpart rf9 p9_581l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_586_1, c9_586_2, c9_586_3, c9_586_4, c9_586_5, c9_586_6, c9_586_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_589r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_589r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_589r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_589r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_590_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_589r) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_590 :
    hubcapFit theRedpart rf9 p9_589r
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_590_1, c9_590_2, c9_590_3, c9_590_4, c9_590_5, c9_590_6, c9_590_7, c9_590_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_589l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_589l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_589l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_589l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_589l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_591_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_589l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_591 :
    hubcapFit theRedpart rf9 p9_589l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_591_1, c9_591_2, c9_591_3, c9_591_4, c9_591_5, c9_591_6, c9_591_7, c9_591_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_588l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_588l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_588l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_588l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_588l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_588l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_593_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_588l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_593 :
    hubcapFit theRedpart rf9 p9_588l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_593_1, c9_593_2, c9_593_3, c9_593_4, c9_593_5, c9_593_6, c9_593_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_576l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_576l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_576l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_576l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_576l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_596_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_576l) (hubSubn 9 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_596 :
    hubcapFit theRedpart rf9 p9_576l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_596_1, c9_596_2, c9_596_3, c9_596_4, c9_596_5, c9_596_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_574l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_574l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_574l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_574l) (hubSubn 9 6 4) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_598_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_574l) (hubSubn 9 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_598 :
    hubcapFit theRedpart rf9 p9_574l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 6 7 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_598_1, c9_598_2, c9_598_3, c9_598_4, c9_598_5, c9_598_6, c9_598_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_605r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_605r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_605r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_605r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_605r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_605r) (hubSubn 9 8 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_606_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_605r) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_606 :
    hubcapFit theRedpart rf9 p9_605r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 5 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_606_1, c9_606_2, c9_606_3, c9_606_4, c9_606_5, c9_606_6, c9_606_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_605l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_605l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_605l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_605l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_605l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_605l) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_607_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_605l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_607 :
    hubcapFit theRedpart rf9 p9_605l
    (Hubcap.one 0 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_607_1, c9_607_2, c9_607_3, c9_607_4, c9_607_5, c9_607_6, c9_607_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_603l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_603l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_603l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_603l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_603l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_603l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_609_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_603l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_609 :
    hubcapFit theRedpart rf9 p9_603l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_609_1, c9_609_2, c9_609_3, c9_609_4, c9_609_5, c9_609_6, c9_609_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_602l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_602l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_602l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_602l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_602l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_611_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_602l) (hubSubn 9 7 6) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_611 :
    hubcapFit theRedpart rf9 p9_602l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_611_1, c9_611_2, c9_611_3, c9_611_4, c9_611_5, c9_611_6, c9_611_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_600l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_600l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_600l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_613_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_600l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_613 :
    hubcapFit theRedpart rf9 p9_600l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_613_1, c9_613_2, c9_613_3, c9_613_4, c9_613_5, c9_613_6, c9_613_7, c9_613_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_571l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_571l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_571l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_571l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_615_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_571l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_615 :
    hubcapFit theRedpart rf9 p9_571l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_615_1, c9_615_2, c9_615_3, c9_615_4, c9_615_5, c9_615_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_569l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_569l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_3 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_569l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_569l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_569l) (hubSubn 9 1 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_569l) (hubSubn 9 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_617_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_569l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_617 :
    hubcapFit theRedpart rf9 p9_569l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.two 0 1 7 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_617_1, c9_617_2, c9_617_3, c9_617_4, c9_617_5, c9_617_6, c9_617_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_568l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_568l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_568l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_568l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 3 p9_568l) (hubSubn 9 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_619_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_568l) (hubSubn 9 7 6) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_619 :
    hubcapFit theRedpart rf9 p9_568l
    (Hubcap.one 2 4 <|
     Hubcap.one 4 5 <|
     Hubcap.one 8 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 3 5 7 <|
     Hubcap.two 6 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_619_1, c9_619_2, c9_619_3, c9_619_4, c9_619_5, c9_619_6]

end FourColor

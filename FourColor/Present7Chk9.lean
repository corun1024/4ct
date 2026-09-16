import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 9 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_510l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_510l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_510l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_510l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_510l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_518_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_510l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_518 :
    hubcapFit theRedpart rf7 p7_510l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_518_1, c7_518_2, c7_518_3, c7_518_4, c7_518_5, c7_518_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_520r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_520r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_520r) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_520r) (hubSubn 7 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_520r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_521_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_520r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_521 :
    hubcapFit theRedpart rf7 p7_520r
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_521_1, c7_521_2, c7_521_3, c7_521_4, c7_521_5, c7_521_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_520l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_520l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_520l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_520l) (hubSubn 7 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_520l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_520l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_522_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_520l) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_522 :
    hubcapFit theRedpart rf7 p7_520l
    (Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_522_1, c7_522_2, c7_522_3, c7_522_4, c7_522_5, c7_522_6, c7_522_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_524_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_444l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_524_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_444l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_524_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_444l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_524_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_444l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_524_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_444l) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_524 :
    hubcapFit theRedpart rf7 p7_444l
    (Hubcap.one 1 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_524_1, c7_524_2, c7_524_3, c7_524_4, c7_524_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_526_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_443l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_526_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_526_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_443l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_526_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_443l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_526_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_443l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_526 :
    hubcapFit theRedpart rf7 p7_443l
    (Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_526_1, c7_526_2, c7_526_3, c7_526_4, c7_526_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_537r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_537r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_537r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_537r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_537r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_538_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_537r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_538 :
    hubcapFit theRedpart rf7 p7_537r
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_538_1, c7_538_2, c7_538_3, c7_538_4, c7_538_5, c7_538_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_539_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_537l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_539_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_537l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_539_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_537l) (hubSubn 7 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_539_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_537l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_539 :
    hubcapFit theRedpart rf7 p7_537l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_539_1, c7_539_2, c7_539_3, c7_539_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_541_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_536l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_541_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_536l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_541_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_536l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_541_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_536l) (hubSubn 7 6 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_541_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_536l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_541 :
    hubcapFit theRedpart rf7 p7_536l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 6 4 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_541_1, c7_541_2, c7_541_3, c7_541_4, c7_541_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_542_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_535l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_542_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_535l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_542_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_535l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_542_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_535l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_542_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_535l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_542 :
    hubcapFit theRedpart rf7 p7_535l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_542_1, c7_542_2, c7_542_3, c7_542_4, c7_542_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_544_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_534l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_544_2 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_534l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_544_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_534l) (hubSubn 7 4 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_544_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_534l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_544 :
    hubcapFit theRedpart rf7 p7_534l
    (Hubcap.one 0 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 3 4 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_544_1, c7_544_2, c7_544_3, c7_544_4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_533l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_533l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_545_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_533l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_545 :
    hubcapFit theRedpart rf7 p7_533l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_545_1, c7_545_2, c7_545_3, c7_545_4, c7_545_5, c7_545_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_532l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_532l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_532l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_547_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_532l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_547 :
    hubcapFit theRedpart rf7 p7_532l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_547_1, c7_547_2, c7_547_3, c7_547_4, c7_547_5, c7_547_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_531l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_531l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_548_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_531l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_548 :
    hubcapFit theRedpart rf7 p7_531l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_548_1, c7_548_2, c7_548_3, c7_548_4, c7_548_5, c7_548_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_530l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_530l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_530l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_550_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_530l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_550 :
    hubcapFit theRedpart rf7 p7_530l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_550_1, c7_550_2, c7_550_3, c7_550_4, c7_550_5, c7_550_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_557r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_557r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_557r) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_557r) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_557r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_557r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_558_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_557r) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_558 :
    hubcapFit theRedpart rf7 p7_557r
    (Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_558_1, c7_558_2, c7_558_3, c7_558_4, c7_558_5, c7_558_6, c7_558_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_557l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_557l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_557l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_557l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_557l) (hubSubn 7 6 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_559_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_557l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_559 :
    hubcapFit theRedpart rf7 p7_557l
    (Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 0 5 4 <|
     Hubcap.two 0 6 4 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_559_1, c7_559_2, c7_559_3, c7_559_4, c7_559_5, c7_559_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_556l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_556l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_556l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_556l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_561_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_556l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_561 :
    hubcapFit theRedpart rf7 p7_556l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_561_1, c7_561_2, c7_561_3, c7_561_4, c7_561_5, c7_561_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_562_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_555l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_562_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_555l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_562_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_555l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_562_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_555l) (hubSubn 7 2 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_562_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_555l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_562 :
    hubcapFit theRedpart rf7 p7_555l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.two 0 2 4 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_562_1, c7_562_2, c7_562_3, c7_562_4, c7_562_5]

end FourColor

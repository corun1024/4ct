import FourColor.Present6Defs
import FourColor.TheQuizTree

/-!
Translated from `present6.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 7 of the arity 6 presentation

One of 8 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_572_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_571r) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_572_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_571r) (hubSubn 6 5 3) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_572_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_571r) (hubSubn 6 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_572 :
    hubcapFit theRedpart rf6 p6_571r
    (Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 (-3) <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_572_1, c6_572_2, c6_572_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_573_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_571l) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_573_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_571l) (hubSubn 6 5 3) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_573_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_571l) (hubSubn 6 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_573 :
    hubcapFit theRedpart rf6 p6_571l
    (Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 (-4) <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_573_1, c6_573_2, c6_573_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_576_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_575r) (hubSubn 6 2 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_576_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_575r) (hubSubn 6 3 1) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_576_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_575r) (hubSubn 6 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_576 :
    hubcapFit theRedpart rf6 p6_575r
    (Hubcap.two 0 2 (-2) <|
     Hubcap.two 1 3 (-2) <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_576_1, c6_576_2, c6_576_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_577_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_575l) (hubSubn 6 2 0) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_577_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_575l) (hubSubn 6 3 1) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_577_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 4 p6_575l) (hubSubn 6 5 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_577 :
    hubcapFit theRedpart rf6 p6_575l
    (Hubcap.two 0 2 (-3) <|
     Hubcap.two 1 3 (-3) <|
     Hubcap.two 4 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_577_1, c6_577_2, c6_577_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_593_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_592r) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_593_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_592r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_593_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_592r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_593 :
    hubcapFit theRedpart rf6 p6_592r
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_593_1, c6_593_2, c6_593_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_594_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_592l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_594_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_592l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_594_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_592l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_594 :
    hubcapFit theRedpart rf6 p6_592l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_594_1, c6_594_2, c6_594_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_597_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_596r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_597_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_596r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_597_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_596r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_597 :
    hubcapFit theRedpart rf6 p6_596r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_597_1, c6_597_2, c6_597_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_598_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_596l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_598_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_596l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_598_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_596l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_598 :
    hubcapFit theRedpart rf6 p6_596l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_598_1, c6_598_2, c6_598_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_600_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_590l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_600_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_590l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_600_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_590l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_600 :
    hubcapFit theRedpart rf6 p6_590l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_600_1, c6_600_2, c6_600_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_603_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_602r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_603_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_602r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_603_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_602r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_603 :
    hubcapFit theRedpart rf6 p6_602r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_603_1, c6_603_2, c6_603_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_604_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_602l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_604_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_602l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_604_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_602l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_604 :
    hubcapFit theRedpart rf6 p6_602l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_604_1, c6_604_2, c6_604_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_606_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_601l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_606_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_601l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_606_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_601l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_606 :
    hubcapFit theRedpart rf6 p6_601l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_606_1, c6_606_2, c6_606_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_608_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_588l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_608_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_588l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_608_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_588l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_608 :
    hubcapFit theRedpart rf6 p6_588l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_608_1, c6_608_2, c6_608_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_611_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_610r) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_611_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_610r) (hubSubn 6 4 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_611_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_610r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_611 :
    hubcapFit theRedpart rf6 p6_610r
    (Hubcap.two 1 2 0 <|
     Hubcap.two 0 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_611_1, c6_611_2, c6_611_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_612_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_609l) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_612_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_609l) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_612_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_609l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_612 :
    hubcapFit theRedpart rf6 p6_609l
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_612_1, c6_612_2, c6_612_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_617_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_616r) (hubSubn 6 2 1) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_617_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_616r) (hubSubn 6 4 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_617_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_616r) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_617 :
    hubcapFit theRedpart rf6 p6_616r
    (Hubcap.two 1 2 1 <|
     Hubcap.two 0 4 (-2) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_617_1, c6_617_2, c6_617_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_618_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 1 p6_616l) (hubSubn 6 2 1) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_618_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_616l) (hubSubn 6 4 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_618_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_616l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_618 :
    hubcapFit theRedpart rf6 p6_616l
    (Hubcap.two 1 2 0 <|
     Hubcap.two 0 4 (-1) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_618_1, c6_618_2, c6_618_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_623_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_622r) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_623_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_622r) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_623_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_622r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_623 :
    hubcapFit theRedpart rf6 p6_622r
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_623_1, c6_623_2, c6_623_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_624_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_622l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_624_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_622l) (hubSubn 6 4 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_624_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_622l) (hubSubn 6 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_624 :
    hubcapFit theRedpart rf6 p6_622l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_624_1, c6_624_2, c6_624_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_627_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_626r) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_627_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_626r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_627_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_626r) (hubSubn 6 5 3) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_627 :
    hubcapFit theRedpart rf6 p6_626r
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_627_1, c6_627_2, c6_627_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_628_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_626l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_628_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_626l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_628_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_626l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_628 :
    hubcapFit theRedpart rf6 p6_626l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_628_1, c6_628_2, c6_628_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_631_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_630r) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_631_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_630r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_631_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_630r) (hubSubn 6 5 3) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_631 :
    hubcapFit theRedpart rf6 p6_630r
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_631_1, c6_631_2, c6_631_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_632_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_630l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_632_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_630l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_632_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_630l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_632 :
    hubcapFit theRedpart rf6 p6_630l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_632_1, c6_632_2, c6_632_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_637_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_636r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_637_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_636r) (hubSubn 6 4 2) (-4)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_637_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_636r) (hubSubn 6 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_637 :
    hubcapFit theRedpart rf6 p6_636r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-4) <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_637_1, c6_637_2, c6_637_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_638_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_636l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_638_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_636l) (hubSubn 6 4 2) (-3)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_638_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_636l) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_638 :
    hubcapFit theRedpart rf6 p6_636l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-3) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_638_1, c6_638_2, c6_638_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_641_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_640r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_641_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_640r) (hubSubn 6 4 2) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_641_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_640r) (hubSubn 6 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_641 :
    hubcapFit theRedpart rf6 p6_640r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 (-2) <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_641_1, c6_641_2, c6_641_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_642_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_640l) (hubSubn 6 1 0) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_642_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_640l) (hubSubn 6 4 2) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_642_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_640l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_642 :
    hubcapFit theRedpart rf6 p6_640l
    (Hubcap.two 0 1 1 <|
     Hubcap.two 2 4 (-1) <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_642_1, c6_642_2, c6_642_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_655_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_654r) (hubSubn 6 1 0) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_655_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_654r) (hubSubn 6 4 2) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_655_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_654r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_655 :
    hubcapFit theRedpart rf6 p6_654r
    (Hubcap.two 0 1 0 <|
     Hubcap.two 2 4 0 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_655_1, c6_655_2, c6_655_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_656_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_654l) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_656_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_654l) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_656_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_654l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_656 :
    hubcapFit theRedpart rf6 p6_654l
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_656_1, c6_656_2, c6_656_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_659_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_658r) (hubSubn 6 1 0) (-1)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_659_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_658r) (hubSubn 6 4 2) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_659_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_658r) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_659 :
    hubcapFit theRedpart rf6 p6_658r
    (Hubcap.two 0 1 (-1) <|
     Hubcap.two 2 4 1 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_659_1, c6_659_2, c6_659_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_660_1 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 0 p6_658l) (hubSubn 6 1 0) (-2)
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_660_2 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 2 p6_658l) (hubSubn 6 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c6_660_3 :
    check2Dbound2 theRedpart rf6
      (hubcapRot 6 3 p6_658l) (hubSubn 6 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f6_660 :
    hubcapFit theRedpart rf6 p6_658l
    (Hubcap.two 0 1 (-2) <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c6_660_1, c6_660_2, c6_660_3]

end FourColor

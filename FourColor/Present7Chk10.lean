import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 10 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_554l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_554l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_554l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_554l) (hubSubn 7 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_554l) (hubSubn 7 6 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_564_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_554l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_564 :
    hubcapFit theRedpart rf7 p7_554l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 0 6 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_564_1, c7_564_2, c7_564_3, c7_564_4, c7_564_5, c7_564_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_553l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_553l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_553l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_553l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_565_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_553l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_565 :
    hubcapFit theRedpart rf7 p7_553l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_565_1, c7_565_2, c7_565_3, c7_565_4, c7_565_5, c7_565_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_552l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_552l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_552l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_552l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_567_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_552l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_567 :
    hubcapFit theRedpart rf7 p7_552l
    (Hubcap.one 0 0 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 2 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_567_1, c7_567_2, c7_567_3, c7_567_4, c7_567_5, c7_567_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_572_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_571r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_572_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_571r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_572_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_571r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_572_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_571r) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_572_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_571r) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_572 :
    hubcapFit theRedpart rf7 p7_571r
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_572_1, c7_572_2, c7_572_3, c7_572_4, c7_572_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_595r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_595r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_596_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_595r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_596 :
    hubcapFit theRedpart rf7 p7_595r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_596_1, c7_596_2, c7_596_3, c7_596_4, c7_596_5, c7_596_6, c7_596_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_595l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_595l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_597_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_595l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_597 :
    hubcapFit theRedpart rf7 p7_595l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_597_1, c7_597_2, c7_597_3, c7_597_4, c7_597_5, c7_597_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_593l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_593l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_599_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_593l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_599 :
    hubcapFit theRedpart rf7 p7_593l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_599_1, c7_599_2, c7_599_3, c7_599_4, c7_599_5, c7_599_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_601_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_590l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_601_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_590l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_601_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_590l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_601_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_590l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_601_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_590l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_601 :
    hubcapFit theRedpart rf7 p7_590l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_601_1, c7_601_2, c7_601_3, c7_601_4, c7_601_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_589l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_589l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_3 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_589l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_589l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_589l) (hubSubn 7 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_603_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_589l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_603 :
    hubcapFit theRedpart rf7 p7_589l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_603_1, c7_603_2, c7_603_3, c7_603_4, c7_603_5, c7_603_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_604_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_588l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_604_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_588l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_604_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_588l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_604_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_588l) (hubSubn 7 4 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_604_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_588l) (hubSubn 7 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_604 :
    hubcapFit theRedpart rf7 p7_588l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 4 2 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_604_1, c7_604_2, c7_604_3, c7_604_4, c7_604_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_606_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_587l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_606_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_587l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_606_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_587l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_606_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_587l) (hubSubn 7 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_606_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_587l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_606 :
    hubcapFit theRedpart rf7 p7_587l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_606_1, c7_606_2, c7_606_3, c7_606_4, c7_606_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_607_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_586l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_607_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_586l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_607_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_586l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_607_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_586l) (hubSubn 7 4 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_607_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_586l) (hubSubn 7 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_607 :
    hubcapFit theRedpart rf7 p7_586l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.two 0 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_607_1, c7_607_2, c7_607_3, c7_607_4, c7_607_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_620r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_620r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_620r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_620r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_620r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_620r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_621_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_620r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_621 :
    hubcapFit theRedpart rf7 p7_620r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_621_1, c7_621_2, c7_621_3, c7_621_4, c7_621_5, c7_621_6, c7_621_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_620l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_620l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_620l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_622_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_620l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_622 :
    hubcapFit theRedpart rf7 p7_620l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_622_1, c7_622_2, c7_622_3, c7_622_4, c7_622_5, c7_622_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_619l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_619l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_619l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_619l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_619l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_624_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_619l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_624 :
    hubcapFit theRedpart rf7 p7_619l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_624_1, c7_624_2, c7_624_3, c7_624_4, c7_624_5, c7_624_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_618l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_625_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_618l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_625 :
    hubcapFit theRedpart rf7 p7_618l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_625_1, c7_625_2, c7_625_3, c7_625_4, c7_625_5, c7_625_6, c7_625_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_616l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_627_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_616l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_627 :
    hubcapFit theRedpart rf7 p7_616l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_627_1, c7_627_2, c7_627_3, c7_627_4, c7_627_5, c7_627_6, c7_627_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_615l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_615l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_629_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_615l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_629 :
    hubcapFit theRedpart rf7 p7_615l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_629_1, c7_629_2, c7_629_3, c7_629_4, c7_629_5, c7_629_6]

end FourColor

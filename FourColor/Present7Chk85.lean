import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 85 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4550l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4550l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4550l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4555_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4550l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4555 :
    hubcapFit theRedpart rf7 p7_4550l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4555_1, c7_4555_2, c7_4555_3, c7_4555_4, c7_4555_5, c7_4555_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4549l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4549l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4549l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4556_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4549l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4556 :
    hubcapFit theRedpart rf7 p7_4549l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4556_1, c7_4556_2, c7_4556_3, c7_4556_4, c7_4556_5, c7_4556_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4548l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4548l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4548l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4558_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4548l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4558 :
    hubcapFit theRedpart rf7 p7_4548l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4558_1, c7_4558_2, c7_4558_3, c7_4558_4, c7_4558_5, c7_4558_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4547l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4547l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4547l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4547l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4547l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4559_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4547l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4559 :
    hubcapFit theRedpart rf7 p7_4547l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4559_1, c7_4559_2, c7_4559_3, c7_4559_4, c7_4559_5, c7_4559_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4546l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4546l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4546l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4546l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4546l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4546l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4561_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4546l) (hubSubn 7 5 3) 0
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4561 :
    hubcapFit theRedpart rf7 p7_4546l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 3 5 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4561_1, c7_4561_2, c7_4561_3, c7_4561_4, c7_4561_5, c7_4561_6, c7_4561_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4563l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4563l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4563l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4563l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4563l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4564_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4563l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4564 :
    hubcapFit theRedpart rf7 p7_4563l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4564_1, c7_4564_2, c7_4564_3, c7_4564_4, c7_4564_5, c7_4564_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4563r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4563r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4563r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4563r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4563r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4566_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4563r) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4566 :
    hubcapFit theRedpart rf7 p7_4563r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4566_1, c7_4566_2, c7_4566_3, c7_4566_4, c7_4566_5, c7_4566_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4543l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4543l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4543l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4569_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4543l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4569 :
    hubcapFit theRedpart rf7 p7_4543l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4569_1, c7_4569_2, c7_4569_3, c7_4569_4, c7_4569_5, c7_4569_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4577r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4577r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4577r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4577r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4577r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4577r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4578_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4577r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4578 :
    hubcapFit theRedpart rf7 p7_4577r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 (-2) <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 5 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4578_1, c7_4578_2, c7_4578_3, c7_4578_4, c7_4578_5, c7_4578_6, c7_4578_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4577l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4577l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4577l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4577l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4577l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4577l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4579_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4577l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4579 :
    hubcapFit theRedpart rf7 p7_4577l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4579_1, c7_4579_2, c7_4579_3, c7_4579_4, c7_4579_5, c7_4579_6, c7_4579_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4576l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4576l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4576l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4576l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4576l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4581_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4576l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4581 :
    hubcapFit theRedpart rf7 p7_4576l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4581_1, c7_4581_2, c7_4581_3, c7_4581_4, c7_4581_5, c7_4581_6, c7_4581_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4583_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4575l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4583_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4575l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4583_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4575l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4583_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4575l) (hubSubn 7 2 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4583_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4575l) (hubSubn 7 5 4) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4583 :
    hubcapFit theRedpart rf7 p7_4575l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 2 2 <|
     Hubcap.two 4 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4583_1, c7_4583_2, c7_4583_3, c7_4583_4, c7_4583_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4589r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4589r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4589r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4589r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4589r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4590_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4589r) (hubSubn 7 5 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4590 :
    hubcapFit theRedpart rf7 p7_4589r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 2 <|
     Hubcap.two 3 5 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4590_1, c7_4590_2, c7_4590_3, c7_4590_4, c7_4590_5, c7_4590_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4603r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4603r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4603r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4604_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4603r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4604 :
    hubcapFit theRedpart rf7 p7_4603r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4604_1, c7_4604_2, c7_4604_3, c7_4604_4, c7_4604_5, c7_4604_6, c7_4604_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4603l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4603l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4603l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4605_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4603l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4605 :
    hubcapFit theRedpart rf7 p7_4603l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4605_1, c7_4605_2, c7_4605_3, c7_4605_4, c7_4605_5, c7_4605_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4602l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4602l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4602l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4607_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4602l) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4607 :
    hubcapFit theRedpart rf7 p7_4602l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4607_1, c7_4607_2, c7_4607_3, c7_4607_4, c7_4607_5, c7_4607_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4609_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4600l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4609_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4600l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4609_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4600l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4609_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4600l) (hubSubn 7 6 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4609_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4600l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4609 :
    hubcapFit theRedpart rf7 p7_4600l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.two 1 6 2 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4609_1, c7_4609_2, c7_4609_3, c7_4609_4, c7_4609_5]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 84 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4487l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4487l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4487l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4487l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4487l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4487l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4492_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4487l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4492 :
    hubcapFit theRedpart rf7 p7_4487l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4492_1, c7_4492_2, c7_4492_3, c7_4492_4, c7_4492_5, c7_4492_6, c7_4492_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4417l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4417l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4417l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4417l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4494_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4417l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4494 :
    hubcapFit theRedpart rf7 p7_4417l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4494_1, c7_4494_2, c7_4494_3, c7_4494_4, c7_4494_5, c7_4494_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4501r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4501r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4501r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4501r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4501r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4502_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4501r) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4502 :
    hubcapFit theRedpart rf7 p7_4501r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4502_1, c7_4502_2, c7_4502_3, c7_4502_4, c7_4502_5, c7_4502_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4501l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4501l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4501l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4501l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4503_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4501l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4503 :
    hubcapFit theRedpart rf7 p7_4501l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4503_1, c7_4503_2, c7_4503_3, c7_4503_4, c7_4503_5, c7_4503_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4500l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4500l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4500l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4500l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4500l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4505_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4500l) (hubSubn 7 5 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4505 :
    hubcapFit theRedpart rf7 p7_4500l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4505_1, c7_4505_2, c7_4505_3, c7_4505_4, c7_4505_5, c7_4505_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4499l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4499l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4499l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4499l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4499l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4499l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4506_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4499l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4506 :
    hubcapFit theRedpart rf7 p7_4499l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4506_1, c7_4506_2, c7_4506_3, c7_4506_4, c7_4506_5, c7_4506_6, c7_4506_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4508_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4497l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4508_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4497l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4508_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4497l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4508_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4497l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4508_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4497l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4508 :
    hubcapFit theRedpart rf7 p7_4497l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4508_1, c7_4508_2, c7_4508_3, c7_4508_4, c7_4508_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4510_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4510_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4510_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4415l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4510_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4415l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4510_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4415l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4510 :
    hubcapFit theRedpart rf7 p7_4415l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.two 3 4 1 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4510_1, c7_4510_2, c7_4510_3, c7_4510_4, c7_4510_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4512_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4414l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4512_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4414l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4512_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4414l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4512_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4414l) (hubSubn 7 5 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4512_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4414l) (hubSubn 7 4 3) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4512 :
    hubcapFit theRedpart rf7 p7_4414l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 6 (-1) <|
     Hubcap.two 2 5 4 <|
     Hubcap.two 3 4 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4512_1, c7_4512_2, c7_4512_3, c7_4512_4, c7_4512_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4413l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4413l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4413l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4413l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4513_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4413l) (hubSubn 7 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4513 :
    hubcapFit theRedpart rf7 p7_4413l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4513_1, c7_4513_2, c7_4513_3, c7_4513_4, c7_4513_5, c7_4513_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4523r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4523r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4523r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4523r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4523r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4524_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4523r) (hubSubn 7 3 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4524 :
    hubcapFit theRedpart rf7 p7_4523r
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4524_1, c7_4524_2, c7_4524_3, c7_4524_4, c7_4524_5, c7_4524_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4536r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4536r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4536r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4536r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4536r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4536r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4537_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4536r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4537 :
    hubcapFit theRedpart rf7 p7_4536r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 5 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-2) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4537_1, c7_4537_2, c7_4537_3, c7_4537_4, c7_4537_5, c7_4537_6, c7_4537_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4536l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4536l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4536l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4536l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4536l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4536l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4538_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4536l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4538 :
    hubcapFit theRedpart rf7 p7_4536l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-2) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4538_1, c7_4538_2, c7_4538_3, c7_4538_4, c7_4538_5, c7_4538_6, c7_4538_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4533l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4533l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4533l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4533l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4533l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4540_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4533l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4540 :
    hubcapFit theRedpart rf7 p7_4533l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 (-1) <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4540_1, c7_4540_2, c7_4540_3, c7_4540_4, c7_4540_5, c7_4540_6, c7_4540_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4542_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4532l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4542_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4532l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4542_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4532l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4542_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4532l) (hubSubn 7 5 1) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4542_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4532l) (hubSubn 7 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4542 :
    hubcapFit theRedpart rf7 p7_4532l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 2 <|
     Hubcap.two 2 3 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4542_1, c7_4542_2, c7_4542_3, c7_4542_4, c7_4542_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4551r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4551r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4551r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4551r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4551r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4552_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4551r) (hubSubn 7 5 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4552 :
    hubcapFit theRedpart rf7 p7_4551r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4552_1, c7_4552_2, c7_4552_3, c7_4552_4, c7_4552_5, c7_4552_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4551l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4551l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4551l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4551l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4551l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4553_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4551l) (hubSubn 7 5 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4553 :
    hubcapFit theRedpart rf7 p7_4551l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 1 <|
     Hubcap.two 3 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4553_1, c7_4553_2, c7_4553_3, c7_4553_4, c7_4553_5, c7_4553_6]

end FourColor

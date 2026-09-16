import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 11 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_614l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_614l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_614l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_630_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_614l) (hubSubn 7 6 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_630 :
    hubcapFit theRedpart rf7 p7_614l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.two 3 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_630_1, c7_630_2, c7_630_3, c7_630_4, c7_630_5, c7_630_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_632_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_632_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_613l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_632_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_613l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_632_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_613l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_632_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_613l) (hubSubn 7 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_632 :
    hubcapFit theRedpart rf7 p7_613l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_632_1, c7_632_2, c7_632_3, c7_632_4, c7_632_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_633_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_612l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_633_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_612l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_633_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_612l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_633_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_612l) (hubSubn 7 3 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_633_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_612l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_633 :
    hubcapFit theRedpart rf7 p7_612l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_633_1, c7_633_2, c7_633_3, c7_633_4, c7_633_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_635_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_610l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_635_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_610l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_635_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_610l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_635_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_610l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_635_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_610l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_635 :
    hubcapFit theRedpart rf7 p7_610l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_635_1, c7_635_2, c7_635_3, c7_635_4, c7_635_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_609l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_609l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_609l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_637_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_609l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_637 :
    hubcapFit theRedpart rf7 p7_609l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_637_1, c7_637_2, c7_637_3, c7_637_4, c7_637_5, c7_637_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_639_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_639_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_583l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_639_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_583l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_639_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_583l) (hubSubn 7 3 0) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_639_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_583l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_639 :
    hubcapFit theRedpart rf7 p7_583l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 2 <|
     Hubcap.two 0 3 2 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_639_1, c7_639_2, c7_639_3, c7_639_4, c7_639_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_640_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_582l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_640_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_582l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_640_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_582l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_640_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_582l) (hubSubn 7 6 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_640_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_582l) (hubSubn 7 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_640 :
    hubcapFit theRedpart rf7 p7_582l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.two 3 6 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_640_1, c7_640_2, c7_640_3, c7_640_4, c7_640_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_581l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_581l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_581l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_581l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_581l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_642_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 3 p7_581l) (hubSubn 7 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_642 :
    hubcapFit theRedpart rf7 p7_581l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_642_1, c7_642_2, c7_642_3, c7_642_4, c7_642_5, c7_642_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_665r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_665r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_665r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_665r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_665r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_665r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_666_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_665r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_666 :
    hubcapFit theRedpart rf7 p7_665r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_666_1, c7_666_2, c7_666_3, c7_666_4, c7_666_5, c7_666_6, c7_666_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_665l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_665l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_667_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_665l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_667 :
    hubcapFit theRedpart rf7 p7_665l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_667_1, c7_667_2, c7_667_3, c7_667_4, c7_667_5, c7_667_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_664l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_664l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_669_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_664l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_669 :
    hubcapFit theRedpart rf7 p7_664l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_669_1, c7_669_2, c7_669_3, c7_669_4, c7_669_5, c7_669_6, c7_669_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_663l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_663l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_671_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_663l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_671 :
    hubcapFit theRedpart rf7 p7_663l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_671_1, c7_671_2, c7_671_3, c7_671_4, c7_671_5, c7_671_6, c7_671_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_662l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_662l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_662l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_662l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_662l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_662l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_673_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_662l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_673 :
    hubcapFit theRedpart rf7 p7_662l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_673_1, c7_673_2, c7_673_3, c7_673_4, c7_673_5, c7_673_6, c7_673_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_661l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_661l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_675_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_675 :
    hubcapFit theRedpart rf7 p7_661l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_675_1, c7_675_2, c7_675_3, c7_675_4, c7_675_5, c7_675_6, c7_675_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_659l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_677_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_659l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_677 :
    hubcapFit theRedpart rf7 p7_659l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_677_1, c7_677_2, c7_677_3, c7_677_4, c7_677_5, c7_677_6, c7_677_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_658l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_658l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_658l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_658l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_658l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_679_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_658l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_679 :
    hubcapFit theRedpart rf7 p7_658l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_679_1, c7_679_2, c7_679_3, c7_679_4, c7_679_5, c7_679_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_657l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_657l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_657l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_657l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_657l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_680_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_657l) (hubSubn 7 5 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_680 :
    hubcapFit theRedpart rf7 p7_657l
    (Hubcap.one 1 1 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 0 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_680_1, c7_680_2, c7_680_3, c7_680_4, c7_680_5, c7_680_6]

end FourColor

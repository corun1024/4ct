import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 14 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_566l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_566l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_566l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_566l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_566l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_621_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_566l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_621 :
    hubcapFit theRedpart rf9 p9_566l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_621_1, c9_621_2, c9_621_3, c9_621_4, c9_621_5, c9_621_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_565l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_565l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_565l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_565l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_565l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_622_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_565l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_622 :
    hubcapFit theRedpart rf9 p9_565l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_622_1, c9_622_2, c9_622_3, c9_622_4, c9_622_5, c9_622_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_564l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_564l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_564l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_564l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_564l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_624_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_564l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_624 :
    hubcapFit theRedpart rf9 p9_564l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_624_1, c9_624_2, c9_624_3, c9_624_4, c9_624_5, c9_624_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_563l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_563l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_563l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_563l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_563l) (hubSubn 9 8 5) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_625_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_563l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_625 :
    hubcapFit theRedpart rf9 p9_563l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 8 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_625_1, c9_625_2, c9_625_3, c9_625_4, c9_625_5, c9_625_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_562l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_562l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_562l) (hubSubn 9 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_562l) (hubSubn 9 8 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_627_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_562l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_627 :
    hubcapFit theRedpart rf9 p9_562l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 8 6 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_627_1, c9_627_2, c9_627_3, c9_627_4, c9_627_5, c9_627_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_638r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_638r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_638r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_638r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_638r) (hubSubn 9 8 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_639_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_638r) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_639 :
    hubcapFit theRedpart rf9 p9_638r
    (Hubcap.one 0 4 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_639_1, c9_639_2, c9_639_3, c9_639_4, c9_639_5, c9_639_6, c9_639_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_638l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_638l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_640_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_638l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_640 :
    hubcapFit theRedpart rf9 p9_638l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_640_1, c9_640_2, c9_640_3, c9_640_4, c9_640_5, c9_640_6, c9_640_7, c9_640_8, c9_640_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_636l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_636l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_636l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_636l) (hubSubn 9 8 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_636l) (hubSubn 9 4 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_642_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_636l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_642 :
    hubcapFit theRedpart rf9 p9_636l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 1 8 7 <|
     Hubcap.two 2 4 6 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_642_1, c9_642_2, c9_642_3, c9_642_4, c9_642_5, c9_642_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_635l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_4 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_635l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_5 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_635l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_644_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_635l) (hubSubn 9 7 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_644 :
    hubcapFit theRedpart rf9 p9_635l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_644_1, c9_644_2, c9_644_3, c9_644_4, c9_644_5, c9_644_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_649r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_649r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_649r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_650_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 4 p9_649r) (hubSubn 9 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_650 :
    hubcapFit theRedpart rf9 p9_649r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_650_1, c9_650_2, c9_650_3, c9_650_4, c9_650_5, c9_650_6, c9_650_7, c9_650_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_649l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_649l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_651_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_649l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_651 :
    hubcapFit theRedpart rf9 p9_649l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_651_1, c9_651_2, c9_651_3, c9_651_4, c9_651_5, c9_651_6, c9_651_7, c9_651_8, c9_651_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_647l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_647l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_647l) (hubSubn 9 8 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_653_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_647l) (hubSubn 9 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_653 :
    hubcapFit theRedpart rf9 p9_647l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 8 7 <|
     Hubcap.two 2 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_653_1, c9_653_2, c9_653_3, c9_653_4, c9_653_5, c9_653_6, c9_653_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_646l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_646l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_646l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_646l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_646l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_646l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_655_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_646l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_655 :
    hubcapFit theRedpart rf9 p9_646l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 1 2 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_655_1, c9_655_2, c9_655_3, c9_655_4, c9_655_5, c9_655_6, c9_655_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_632l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_632l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_657_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_632l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_657 :
    hubcapFit theRedpart rf9 p9_632l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_657_1, c9_657_2, c9_657_3, c9_657_4, c9_657_5, c9_657_6, c9_657_7, c9_657_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_631l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_631l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_631l) (hubSubn 9 2 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_659_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_631l) (hubSubn 9 7 6) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_659 :
    hubcapFit theRedpart rf9 p9_631l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 3 <|
     Hubcap.one 8 3 <|
     Hubcap.two 1 2 7 <|
     Hubcap.two 6 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_659_1, c9_659_2, c9_659_3, c9_659_4, c9_659_5, c9_659_6, c9_659_7]

end FourColor

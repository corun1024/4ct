import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 106 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5611l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5611l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5611l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5611l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5611l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5611l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5617_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5611l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5617 :
    hubcapFit theRedpart rf7 p7_5611l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5617_1, c7_5617_2, c7_5617_3, c7_5617_4, c7_5617_5, c7_5617_6, c7_5617_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5610l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5610l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5610l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5610l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5610l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5610l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5619_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5610l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5619 :
    hubcapFit theRedpart rf7 p7_5610l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5619_1, c7_5619_2, c7_5619_3, c7_5619_4, c7_5619_5, c7_5619_6, c7_5619_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5636r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5636r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5636r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5636r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5636r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5636r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5637_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5636r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5637 :
    hubcapFit theRedpart rf7 p7_5636r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-4) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5637_1, c7_5637_2, c7_5637_3, c7_5637_4, c7_5637_5, c7_5637_6, c7_5637_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5645r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5645r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5645r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5645r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5645r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5645r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5646_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5645r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5646 :
    hubcapFit theRedpart rf7 p7_5645r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 (-2) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5646_1, c7_5646_2, c7_5646_3, c7_5646_4, c7_5646_5, c7_5646_6, c7_5646_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5645l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5645l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5645l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5645l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5645l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5645l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5647_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5645l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5647 :
    hubcapFit theRedpart rf7 p7_5645l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5647_1, c7_5647_2, c7_5647_3, c7_5647_4, c7_5647_5, c7_5647_6, c7_5647_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5644l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5644l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5644l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5644l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5644l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5649_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5644l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5649 :
    hubcapFit theRedpart rf7 p7_5644l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5649_1, c7_5649_2, c7_5649_3, c7_5649_4, c7_5649_5, c7_5649_6, c7_5649_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5643l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5643l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5643l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5643l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5643l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5643l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5651_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5643l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5651 :
    hubcapFit theRedpart rf7 p7_5643l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 0 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5651_1, c7_5651_2, c7_5651_3, c7_5651_4, c7_5651_5, c7_5651_6, c7_5651_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5641l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5641l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5653_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5641l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5653 :
    hubcapFit theRedpart rf7 p7_5641l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5653_1, c7_5653_2, c7_5653_3, c7_5653_4, c7_5653_5, c7_5653_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5640l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5640l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5655_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5640l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5655 :
    hubcapFit theRedpart rf7 p7_5640l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5655_1, c7_5655_2, c7_5655_3, c7_5655_4, c7_5655_5, c7_5655_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5661r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5661r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5661r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5661r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5661r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5661r) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5662_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5661r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5662 :
    hubcapFit theRedpart rf7 p7_5661r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-4) <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5662_1, c7_5662_2, c7_5662_3, c7_5662_4, c7_5662_5, c7_5662_6, c7_5662_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5661l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5661l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5661l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5661l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5661l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5663_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5661l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5663 :
    hubcapFit theRedpart rf7 p7_5661l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5663_1, c7_5663_2, c7_5663_3, c7_5663_4, c7_5663_5, c7_5663_6, c7_5663_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5660l) (-4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5660l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5660l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5665_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5660l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5665 :
    hubcapFit theRedpart rf7 p7_5660l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-4) <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5665_1, c7_5665_2, c7_5665_3, c7_5665_4, c7_5665_5, c7_5665_6, c7_5665_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5657l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5657l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5657l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5657l) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5657l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5667_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5657l) (hubSubn 7 3 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5667 :
    hubcapFit theRedpart rf7 p7_5657l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 (-3) <|
     Hubcap.one 6 2 <|
     Hubcap.two 0 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5667_1, c7_5667_2, c7_5667_3, c7_5667_4, c7_5667_5, c7_5667_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5683r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5683r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5683r) (-3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5683r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5683r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5683r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5684_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5683r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5684 :
    hubcapFit theRedpart rf7 p7_5683r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-3) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5684_1, c7_5684_2, c7_5684_3, c7_5684_4, c7_5684_5, c7_5684_6, c7_5684_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5683l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5683l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5683l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5683l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5683l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5685_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5683l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5685 :
    hubcapFit theRedpart rf7 p7_5683l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5685_1, c7_5685_2, c7_5685_3, c7_5685_4, c7_5685_5, c7_5685_6, c7_5685_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5682l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5682l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5682l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5682l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5682l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5687_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5682l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5687 :
    hubcapFit theRedpart rf7 p7_5682l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 (-2) <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5687_1, c7_5687_2, c7_5687_3, c7_5687_4, c7_5687_5, c7_5687_6, c7_5687_7]

end FourColor

import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 98 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5186l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5186l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5186l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5186l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5200_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5186l) (hubSubn 7 6 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5200 :
    hubcapFit theRedpart rf7 p7_5186l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 4 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5200_1, c7_5200_2, c7_5200_3, c7_5200_4, c7_5200_5, c7_5200_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5185l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5185l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5185l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5185l) (hubSubn 7 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5185l) (hubSubn 7 6 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5201_7 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5185l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5201 :
    hubcapFit theRedpart rf7 p7_5185l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 (-1) <|
     Hubcap.one 3 2 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 4 6 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5201_1, c7_5201_2, c7_5201_3, c7_5201_4, c7_5201_5, c7_5201_6, c7_5201_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5204_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4983l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5204_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4983l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5204_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4983l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5204_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4983l) (hubSubn 7 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5204_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4983l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5204 :
    hubcapFit theRedpart rf7 p7_4983l
    (Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5204_1, c7_5204_2, c7_5204_3, c7_5204_4, c7_5204_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5219r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5219r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5219r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5219r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5219r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5219r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5220_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5219r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5220 :
    hubcapFit theRedpart rf7 p7_5219r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5220_1, c7_5220_2, c7_5220_3, c7_5220_4, c7_5220_5, c7_5220_6, c7_5220_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5219l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5219l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5219l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5219l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5219l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5219l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5221_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5219l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5221 :
    hubcapFit theRedpart rf7 p7_5219l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5221_1, c7_5221_2, c7_5221_3, c7_5221_4, c7_5221_5, c7_5221_6, c7_5221_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5217l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5217l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5217l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5223_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5217l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5223 :
    hubcapFit theRedpart rf7 p7_5217l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5223_1, c7_5223_2, c7_5223_3, c7_5223_4, c7_5223_5, c7_5223_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5225_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5216l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5225 :
    hubcapFit theRedpart rf7 p7_5216l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5225_1, c7_5225_2, c7_5225_3, c7_5225_4, c7_5225_5, c7_5225_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5215l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5215l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5215l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5215l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5226_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5215l) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5226 :
    hubcapFit theRedpart rf7 p7_5215l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5226_1, c7_5226_2, c7_5226_3, c7_5226_4, c7_5226_5, c7_5226_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5213l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5213l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5213l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5213l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5228_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5213l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5228 :
    hubcapFit theRedpart rf7 p7_5213l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5228_1, c7_5228_2, c7_5228_3, c7_5228_4, c7_5228_5, c7_5228_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5212l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5212l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5212l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5212l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5230_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5212l) (hubSubn 7 6 5) 1
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5230 :
    hubcapFit theRedpart rf7 p7_5212l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.two 5 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5230_1, c7_5230_2, c7_5230_3, c7_5230_4, c7_5230_5, c7_5230_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5242r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5242r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5242r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5242r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5242r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5242r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5243_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5242r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5243 :
    hubcapFit theRedpart rf7 p7_5242r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 (-1) <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5243_1, c7_5243_2, c7_5243_3, c7_5243_4, c7_5243_5, c7_5243_6, c7_5243_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5242l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5242l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5242l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5244_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5242l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5244 :
    hubcapFit theRedpart rf7 p7_5242l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5244_1, c7_5244_2, c7_5244_3, c7_5244_4, c7_5244_5, c7_5244_6, c7_5244_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5240l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5240l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5240l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5246_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5240l) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5246 :
    hubcapFit theRedpart rf7 p7_5240l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5246_1, c7_5246_2, c7_5246_3, c7_5246_4, c7_5246_5, c7_5246_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5248r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5248r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5248r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5248r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5248r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5249_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5248r) (hubSubn 7 6 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5249 :
    hubcapFit theRedpart rf7 p7_5248r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5249_1, c7_5249_2, c7_5249_3, c7_5249_4, c7_5249_5, c7_5249_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5256r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5256r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5256r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5256r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5256r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5257_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5256r) (hubSubn 7 6 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5257 :
    hubcapFit theRedpart rf7 p7_5256r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5257_1, c7_5257_2, c7_5257_3, c7_5257_4, c7_5257_5, c7_5257_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5261r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5261r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5261r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5261r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5261r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5262_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5261r) (hubSubn 7 6 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5262 :
    hubcapFit theRedpart rf7 p7_5261r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 2 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5262_1, c7_5262_2, c7_5262_3, c7_5262_4, c7_5262_5, c7_5262_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_5261l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_5261l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_5261l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_5261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_5261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_5261l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_5263_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_5261l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_5263 :
    hubcapFit theRedpart rf7 p7_5261l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_5263_1, c7_5263_2, c7_5263_3, c7_5263_4, c7_5263_5, c7_5263_6, c7_5263_7]

end FourColor

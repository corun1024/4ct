import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 44 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2243l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2243l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2243l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2243l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2243l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2243l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2249_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2243l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2249 :
    hubcapFit theRedpart rf8 p8_2243l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2249_1, c8_2249_2, c8_2249_3, c8_2249_4, c8_2249_5, c8_2249_6, c8_2249_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2242l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2242l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2242l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2251_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2242l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2251 :
    hubcapFit theRedpart rf8 p8_2242l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2251_1, c8_2251_2, c8_2251_3, c8_2251_4, c8_2251_5, c8_2251_6, c8_2251_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2241l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2241l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2241l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2241l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2241l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2241l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2241l) (hubSubn 8 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2253_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2241l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2253 :
    hubcapFit theRedpart rf8 p8_2241l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 1 3 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2253_1, c8_2253_2, c8_2253_3, c8_2253_4, c8_2253_5, c8_2253_6, c8_2253_7, c8_2253_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2240l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2240l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2240l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2240l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2240l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2240l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2240l) (hubSubn 8 3 1) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2255_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2240l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2255 :
    hubcapFit theRedpart rf8 p8_2240l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 1 3 7 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2255_1, c8_2255_2, c8_2255_3, c8_2255_4, c8_2255_5, c8_2255_6, c8_2255_7, c8_2255_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2238l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2238l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2238l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2257_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2238l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2257 :
    hubcapFit theRedpart rf8 p8_2238l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2257_1, c8_2257_2, c8_2257_3, c8_2257_4, c8_2257_5, c8_2257_6, c8_2257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2237l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2237l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2237l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2237l) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2259_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2237l) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2259 :
    hubcapFit theRedpart rf8 p8_2237l
    (Hubcap.one 0 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 5 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2259_1, c8_2259_2, c8_2259_3, c8_2259_4, c8_2259_5, c8_2259_6, c8_2259_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2236l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2236l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2236l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2261_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2236l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2261 :
    hubcapFit theRedpart rf8 p8_2236l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2261_1, c8_2261_2, c8_2261_3, c8_2261_4, c8_2261_5, c8_2261_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2262_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2235l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2262_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2235l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2262_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2235l) (hubSubn 8 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2262_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2235l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2262_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2235l) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2262 :
    hubcapFit theRedpart rf8 p8_2235l
    (Hubcap.one 4 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2262_1, c8_2262_2, c8_2262_3, c8_2262_4, c8_2262_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2268_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2267r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2268_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2267r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2268_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2267r) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2268_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2267r) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2268_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2267r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2268 :
    hubcapFit theRedpart rf8 p8_2267r
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2268_1, c8_2268_2, c8_2268_3, c8_2268_4, c8_2268_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2267l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2267l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2267l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2267l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2267l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2267l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2269_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2267l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2269 :
    hubcapFit theRedpart rf8 p8_2267l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 0 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2269_1, c8_2269_2, c8_2269_3, c8_2269_4, c8_2269_5, c8_2269_6, c8_2269_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2266l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2266l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2266l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2266l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2266l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2271_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2266l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2271 :
    hubcapFit theRedpart rf8 p8_2266l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2271_1, c8_2271_2, c8_2271_3, c8_2271_4, c8_2271_5, c8_2271_6, c8_2271_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2265l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2273_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2265l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2273 :
    hubcapFit theRedpart rf8 p8_2265l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2273_1, c8_2273_2, c8_2273_3, c8_2273_4, c8_2273_5, c8_2273_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2264l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2264l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2274_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2264l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2274 :
    hubcapFit theRedpart rf8 p8_2264l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2274_1, c8_2274_2, c8_2274_3, c8_2274_4, c8_2274_5, c8_2274_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2286r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2286r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2286r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2286r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2286r) (hubSubn 8 3 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2287_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2286r) (hubSubn 8 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2287 :
    hubcapFit theRedpart rf8 p8_2286r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 2 3 7 <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2287_1, c8_2287_2, c8_2287_3, c8_2287_4, c8_2287_5, c8_2287_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2286l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2286l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2288_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2286l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2288 :
    hubcapFit theRedpart rf8 p8_2286l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2288_1, c8_2288_2, c8_2288_3, c8_2288_4, c8_2288_5, c8_2288_6, c8_2288_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2285l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2285l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2285l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_2290_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2285l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_2290 :
    hubcapFit theRedpart rf8 p8_2285l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 1 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_2290_1, c8_2290_2, c8_2290_3, c8_2290_4, c8_2290_5, c8_2290_6, c8_2290_7]

end FourColor

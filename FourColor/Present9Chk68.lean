import FourColor.Present9Defs
import FourColor.TheQuizTree

/-!
Translated from `present9.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 68 of the arity 9 presentation

One of 77 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3210l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3210l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3210l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3210l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3218_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3210l) (hubSubn 9 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3218 :
    hubcapFit theRedpart rf9 p9_3210l
    (Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3218_1, c9_3218_2, c9_3218_3, c9_3218_4, c9_3218_5, c9_3218_6, c9_3218_7, c9_3218_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3208l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3208l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3208l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3208l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3208l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3208l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3220_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3208l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3220 :
    hubcapFit theRedpart rf9 p9_3208l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3220_1, c9_3220_2, c9_3220_3, c9_3220_4, c9_3220_5, c9_3220_6, c9_3220_7, c9_3220_8, c9_3220_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3206l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3206l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3206l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3222_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3222 :
    hubcapFit theRedpart rf9 p9_3206l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3222_1, c9_3222_2, c9_3222_3, c9_3222_4, c9_3222_5, c9_3222_6, c9_3222_7, c9_3222_8, c9_3222_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3224l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3224l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3224l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3224l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3224l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3224l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3225_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3224l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3225 :
    hubcapFit theRedpart rf9 p9_3224l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3225_1, c9_3225_2, c9_3225_3, c9_3225_4, c9_3225_5, c9_3225_6, c9_3225_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3224r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3224r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3224r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3224r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3224r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3224r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3227_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3224r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3227 :
    hubcapFit theRedpart rf9 p9_3224r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3227_1, c9_3227_2, c9_3227_3, c9_3227_4, c9_3227_5, c9_3227_6, c9_3227_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3175l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3175l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3175l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3230_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3175l) (hubSubn 9 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3230 :
    hubcapFit theRedpart rf9 p9_3175l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3230_1, c9_3230_2, c9_3230_3, c9_3230_4, c9_3230_5, c9_3230_6, c9_3230_7, c9_3230_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3174l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3174l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3174l) (hubSubn 9 1 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3232_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3174l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3232 :
    hubcapFit theRedpart rf9 p9_3174l
    (Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3232_1, c9_3232_2, c9_3232_3, c9_3232_4, c9_3232_5, c9_3232_6, c9_3232_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3234l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3234l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3234l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3234l) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3235_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3234l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3235 :
    hubcapFit theRedpart rf9 p9_3234l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3235_1, c9_3235_2, c9_3235_3, c9_3235_4, c9_3235_5, c9_3235_6, c9_3235_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3234r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3234r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3234r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3234r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3234r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3234r) (hubSubn 9 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3237_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3234r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3237 :
    hubcapFit theRedpart rf9 p9_3234r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 7 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3237_1, c9_3237_2, c9_3237_3, c9_3237_4, c9_3237_5, c9_3237_6, c9_3237_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3172l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3172l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_8 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3172l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3240_9 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 8 p9_3172l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3240 :
    hubcapFit theRedpart rf9 p9_3172l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 5 <|
     Hubcap.one 8 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3240_1, c9_3240_2, c9_3240_3, c9_3240_4, c9_3240_5, c9_3240_6, c9_3240_7, c9_3240_8, c9_3240_9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3249r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3249r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3249r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3249r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3249r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3249r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3249r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3250_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3249r) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3250 :
    hubcapFit theRedpart rf9 p9_3249r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3250_1, c9_3250_2, c9_3250_3, c9_3250_4, c9_3250_5, c9_3250_6, c9_3250_7, c9_3250_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3249l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3249l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3249l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_6 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3249l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_7 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3249l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3251_8 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3249l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3251 :
    hubcapFit theRedpart rf9 p9_3249l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 1 <|
     Hubcap.one 7 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3251_1, c9_3251_2, c9_3251_3, c9_3251_4, c9_3251_5, c9_3251_6, c9_3251_7, c9_3251_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3248l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3248l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3248l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3248l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3248l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3248l) (hubSubn 9 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3253_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 6 p9_3248l) (hubSubn 9 8 6) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3253 :
    hubcapFit theRedpart rf9 p9_3248l
    (Hubcap.one 2 5 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 6 8 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3253_1, c9_3253_2, c9_3253_3, c9_3253_4, c9_3253_5, c9_3253_6, c9_3253_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_1 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 1 p9_3247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_2 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 2 p9_3247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_3 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 3 p9_3247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_4 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 4 p9_3247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_5 :
    checkDbound2 theRedpart rf9
      (hubcapRot 9 7 p9_3247l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_6 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 0 p9_3247l) (hubSubn 9 8 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c9_3255_7 :
    check2Dbound2 theRedpart rf9
      (hubcapRot 9 5 p9_3247l) (hubSubn 9 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f9_3255 :
    hubcapFit theRedpart rf9 p9_3247l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 4 <|
     Hubcap.one 7 5 <|
     Hubcap.two 0 8 7 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c9_3255_1, c9_3255_2, c9_3255_3, c9_3255_4, c9_3255_5, c9_3255_6, c9_3255_7]

end FourColor

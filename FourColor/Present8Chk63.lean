import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 63 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3207_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3171l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3207_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3171l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3207_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3171l) (hubSubn 8 5 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3207_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3171l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3207_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3171l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3207 :
    hubcapFit theRedpart rf8 p8_3171l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 5 5 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3207_1, c8_3207_2, c8_3207_3, c8_3207_4, c8_3207_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3217r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3217r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3218_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3217r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3218 :
    hubcapFit theRedpart rf8 p8_3217r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3218_1, c8_3218_2, c8_3218_3, c8_3218_4, c8_3218_5, c8_3218_6, c8_3218_7, c8_3218_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3217l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3217l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3217l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3219_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3217l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3219 :
    hubcapFit theRedpart rf8 p8_3217l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3219_1, c8_3219_2, c8_3219_3, c8_3219_4, c8_3219_5, c8_3219_6, c8_3219_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3216l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3216l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3221_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3216l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3221 :
    hubcapFit theRedpart rf8 p8_3216l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3221_1, c8_3221_2, c8_3221_3, c8_3221_4, c8_3221_5, c8_3221_6, c8_3221_7, c8_3221_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3214l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3214l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3214l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3223_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3214l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3223 :
    hubcapFit theRedpart rf8 p8_3214l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3223_1, c8_3223_2, c8_3223_3, c8_3223_4, c8_3223_5, c8_3223_6, c8_3223_7, c8_3223_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3213l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3213l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3213l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3213l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3225_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3213l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3225 :
    hubcapFit theRedpart rf8 p8_3213l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.two 2 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3225_1, c8_3225_2, c8_3225_3, c8_3225_4, c8_3225_5, c8_3225_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3212l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3212l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3212l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3212l) (hubSubn 8 5 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3226_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3212l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3226 :
    hubcapFit theRedpart rf8 p8_3212l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3226_1, c8_3226_2, c8_3226_3, c8_3226_4, c8_3226_5, c8_3226_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3211l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3211l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3211l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3211l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3211l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3228_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3211l) (hubSubn 8 5 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3228 :
    hubcapFit theRedpart rf8 p8_3211l
    (Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3228_1, c8_3228_2, c8_3228_3, c8_3228_4, c8_3228_5, c8_3228_6, c8_3228_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3210l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3210l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3210l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3210l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3210l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3210l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3210l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3230_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3210l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3230 :
    hubcapFit theRedpart rf8 p8_3210l
    (Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3230_1, c8_3230_2, c8_3230_3, c8_3230_4, c8_3230_5, c8_3230_6, c8_3230_7, c8_3230_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3209l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3209l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3209l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3209l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3209l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3209l) (hubSubn 8 5 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3232_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3209l) (hubSubn 8 5 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3232 :
    hubcapFit theRedpart rf8 p8_3209l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 5 6 <|
     Hubcap.two 3 5 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3232_1, c8_3232_2, c8_3232_3, c8_3232_4, c8_3232_5, c8_3232_6, c8_3232_7, c8_3232_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3168l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3168l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3168l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3168l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3234_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3168l) (hubSubn 8 5 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3234 :
    hubcapFit theRedpart rf8 p8_3168l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 4 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3234_1, c8_3234_2, c8_3234_3, c8_3234_4, c8_3234_5, c8_3234_6, c8_3234_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3253r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3253r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3253r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3253r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3253r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3253r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3253r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3254_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3253r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3254 :
    hubcapFit theRedpart rf8 p8_3253r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3254_1, c8_3254_2, c8_3254_3, c8_3254_4, c8_3254_5, c8_3254_6, c8_3254_7, c8_3254_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3253l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3253l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3253l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3253l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3253l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3253l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3253l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3255_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3253l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3255 :
    hubcapFit theRedpart rf8 p8_3253l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3255_1, c8_3255_2, c8_3255_3, c8_3255_4, c8_3255_5, c8_3255_6, c8_3255_7, c8_3255_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3252l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3252l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3252l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3252l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3252l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3252l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3257_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3252l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3257 :
    hubcapFit theRedpart rf8 p8_3252l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3257_1, c8_3257_2, c8_3257_3, c8_3257_4, c8_3257_5, c8_3257_6, c8_3257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3251l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3251l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3251l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3251l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3259_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3251l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3259 :
    hubcapFit theRedpart rf8 p8_3251l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3259_1, c8_3259_2, c8_3259_3, c8_3259_4, c8_3259_5, c8_3259_6, c8_3259_7]

end FourColor

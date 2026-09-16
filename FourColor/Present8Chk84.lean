import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 84 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4200l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4200l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4200l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4200l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4202_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4200l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4202 :
    hubcapFit theRedpart rf8 p8_4200l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4202_1, c8_4202_2, c8_4202_3, c8_4202_4, c8_4202_5, c8_4202_6, c8_4202_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4198l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4198l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4198l) (hubSubn 8 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4198l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4198l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4204_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4198l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4204 :
    hubcapFit theRedpart rf8 p8_4198l
    (Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4204_1, c8_4204_2, c8_4204_3, c8_4204_4, c8_4204_5, c8_4204_6, c8_4204_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4207r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4207r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4207r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4207r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4207r) (hubSubn 8 5 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4208_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4207r) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4208 :
    hubcapFit theRedpart rf8 p8_4207r
    (Hubcap.one 2 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 5 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4208_1, c8_4208_2, c8_4208_3, c8_4208_4, c8_4208_5, c8_4208_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4207l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4207l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4207l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4207l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4207l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4209_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4207l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4209 :
    hubcapFit theRedpart rf8 p8_4207l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4209_1, c8_4209_2, c8_4209_3, c8_4209_4, c8_4209_5, c8_4209_6, c8_4209_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4206l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4206l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4206l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4206l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4211_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4206l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4211 :
    hubcapFit theRedpart rf8 p8_4206l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4211_1, c8_4211_2, c8_4211_3, c8_4211_4, c8_4211_5, c8_4211_6, c8_4211_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4213_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4171l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4213_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4171l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4213_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4171l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4213_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4171l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4213_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4171l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4213 :
    hubcapFit theRedpart rf8 p8_4171l
    (Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4213_1, c8_4213_2, c8_4213_3, c8_4213_4, c8_4213_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4095l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4095l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4095l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4095l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4095l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4095l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4216_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4095l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4216 :
    hubcapFit theRedpart rf8 p8_4095l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4216_1, c8_4216_2, c8_4216_3, c8_4216_4, c8_4216_5, c8_4216_6, c8_4216_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4240r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4240r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4240r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4240r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4240r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4241_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4240r) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4241 :
    hubcapFit theRedpart rf8 p8_4240r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4241_1, c8_4241_2, c8_4241_3, c8_4241_4, c8_4241_5, c8_4241_6, c8_4241_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4240l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4240l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4240l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4240l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4240l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4242_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4240l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4242 :
    hubcapFit theRedpart rf8 p8_4240l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4242_1, c8_4242_2, c8_4242_3, c8_4242_4, c8_4242_5, c8_4242_6, c8_4242_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4236l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4236l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4236l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4236l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4236l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4244_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4236l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4244 :
    hubcapFit theRedpart rf8 p8_4236l
    (Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4244_1, c8_4244_2, c8_4244_3, c8_4244_4, c8_4244_5, c8_4244_6, c8_4244_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4249r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4249r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4249r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4249r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4249r) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4250_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4249r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4250 :
    hubcapFit theRedpart rf8 p8_4249r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4250_1, c8_4250_2, c8_4250_3, c8_4250_4, c8_4250_5, c8_4250_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4249l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4249l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4249l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4251_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4249l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4251 :
    hubcapFit theRedpart rf8 p8_4249l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4251_1, c8_4251_2, c8_4251_3, c8_4251_4, c8_4251_5, c8_4251_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4248l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4248l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4248l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4248l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4248l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4248l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4253_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4248l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4253 :
    hubcapFit theRedpart rf8 p8_4248l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4253_1, c8_4253_2, c8_4253_3, c8_4253_4, c8_4253_5, c8_4253_6, c8_4253_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4247l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4247l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4247l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4255_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4247l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4255 :
    hubcapFit theRedpart rf8 p8_4247l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4255_1, c8_4255_2, c8_4255_3, c8_4255_4, c8_4255_5, c8_4255_6, c8_4255_7, c8_4255_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4246l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4246l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4246l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4246l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4257_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4246l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4257 :
    hubcapFit theRedpart rf8 p8_4246l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4257_1, c8_4257_2, c8_4257_3, c8_4257_4, c8_4257_5, c8_4257_6, c8_4257_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4234l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4234l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4234l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4234l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4234l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4259_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4234l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4259 :
    hubcapFit theRedpart rf8 p8_4234l
    (Hubcap.one 6 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 7 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4259_1, c8_4259_2, c8_4259_3, c8_4259_4, c8_4259_5, c8_4259_6]

end FourColor

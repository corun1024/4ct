import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 81 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4047l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4047l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4047l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4070_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4047l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4070 :
    hubcapFit theRedpart rf8 p8_4047l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4070_1, c8_4070_2, c8_4070_3, c8_4070_4, c8_4070_5, c8_4070_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4046l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4046l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4046l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4071_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4046l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4071 :
    hubcapFit theRedpart rf8 p8_4046l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4071_1, c8_4071_2, c8_4071_3, c8_4071_4, c8_4071_5, c8_4071_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4031l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4031l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4031l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4031l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4073_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4031l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4073 :
    hubcapFit theRedpart rf8 p8_4031l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4073_1, c8_4073_2, c8_4073_3, c8_4073_4, c8_4073_5, c8_4073_6, c8_4073_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4030l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4030l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4030l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4030l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4075_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4030l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4075 :
    hubcapFit theRedpart rf8 p8_4030l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4075_1, c8_4075_2, c8_4075_3, c8_4075_4, c8_4075_5, c8_4075_6, c8_4075_7, c8_4075_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4029l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4029l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4029l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4077_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4029l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4077 :
    hubcapFit theRedpart rf8 p8_4029l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4077_1, c8_4077_2, c8_4077_3, c8_4077_4, c8_4077_5, c8_4077_6, c8_4077_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4027l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4027l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4027l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4079_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4027l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4079 :
    hubcapFit theRedpart rf8 p8_4027l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4079_1, c8_4079_2, c8_4079_3, c8_4079_4, c8_4079_5, c8_4079_6, c8_4079_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4026l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4026l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4026l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4081_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4026l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4081 :
    hubcapFit theRedpart rf8 p8_4026l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4081_1, c8_4081_2, c8_4081_3, c8_4081_4, c8_4081_5, c8_4081_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4025l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4025l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4025l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4025l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4025l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4025l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4082_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4025l) (hubSubn 8 5 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4082 :
    hubcapFit theRedpart rf8 p8_4025l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 5 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4082_1, c8_4082_2, c8_4082_3, c8_4082_4, c8_4082_5, c8_4082_6, c8_4082_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4024l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4024l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4024l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4024l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4084_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4024l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4084 :
    hubcapFit theRedpart rf8 p8_4024l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4084_1, c8_4084_2, c8_4084_3, c8_4084_4, c8_4084_5, c8_4084_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4001l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4001l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4001l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4001l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4086_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4001l) (hubSubn 8 4 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4086 :
    hubcapFit theRedpart rf8 p8_4001l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 3 4 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4086_1, c8_4086_2, c8_4086_3, c8_4086_4, c8_4086_5, c8_4086_6, c8_4086_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4088_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4000l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4088_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4000l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4088_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4000l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4088_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4000l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4088_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4000l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4088 :
    hubcapFit theRedpart rf8 p8_4000l
    (Hubcap.one 4 2 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4088_1, c8_4088_2, c8_4088_3, c8_4088_4, c8_4088_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3920l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3920l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3920l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3920l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4090_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3920l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4090 :
    hubcapFit theRedpart rf8 p8_3920l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4090_1, c8_4090_2, c8_4090_3, c8_4090_4, c8_4090_5, c8_4090_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3919l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3919l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3919l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3919l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4091_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3919l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4091 :
    hubcapFit theRedpart rf8 p8_3919l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4091_1, c8_4091_2, c8_4091_3, c8_4091_4, c8_4091_5, c8_4091_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3918l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3918l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3918l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4093_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3918l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4093 :
    hubcapFit theRedpart rf8 p8_3918l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4093_1, c8_4093_2, c8_4093_3, c8_4093_4, c8_4093_5, c8_4093_6, c8_4093_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4106r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4106r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4106r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4106r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4106r) (hubSubn 8 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4107_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4106r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4107 :
    hubcapFit theRedpart rf8 p8_4106r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4107_1, c8_4107_2, c8_4107_3, c8_4107_4, c8_4107_5, c8_4107_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4106l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4106l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4106l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4106l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4106l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4106l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4108_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4106l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4108 :
    hubcapFit theRedpart rf8 p8_4106l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4108_1, c8_4108_2, c8_4108_3, c8_4108_4, c8_4108_5, c8_4108_6, c8_4108_7]

end FourColor

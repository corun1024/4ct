import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 61 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3109r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3109r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3109r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3109r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3109r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3109r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3110_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3109r) (hubSubn 8 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3110 :
    hubcapFit theRedpart rf8 p8_3109r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 5 4 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3110_1, c8_3110_2, c8_3110_3, c8_3110_4, c8_3110_5, c8_3110_6, c8_3110_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3109l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3109l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3109l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3109l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3109l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3111_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3109l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3111 :
    hubcapFit theRedpart rf8 p8_3109l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3111_1, c8_3111_2, c8_3111_3, c8_3111_4, c8_3111_5, c8_3111_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3108l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3108l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3113_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3108l) (hubSubn 8 6 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3113 :
    hubcapFit theRedpart rf8 p8_3108l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3113_1, c8_3113_2, c8_3113_3, c8_3113_4, c8_3113_5, c8_3113_6, c8_3113_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3107l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3107l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3107l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3107l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3107l) (hubSubn 8 6 3) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3115_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3107l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3115 :
    hubcapFit theRedpart rf8 p8_3107l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 7 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3115_1, c8_3115_2, c8_3115_3, c8_3115_4, c8_3115_5, c8_3115_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3106l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3106l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3106l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3106l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3106l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3116_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3106l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3116 :
    hubcapFit theRedpart rf8 p8_3106l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3116_1, c8_3116_2, c8_3116_3, c8_3116_4, c8_3116_5, c8_3116_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3118_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3104l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3118_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3104l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3118_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3104l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3118_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3104l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3118_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3104l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3118 :
    hubcapFit theRedpart rf8 p8_3104l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3118_1, c8_3118_2, c8_3118_3, c8_3118_4, c8_3118_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3041l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3041l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3041l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3041l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3120_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3041l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3120 :
    hubcapFit theRedpart rf8 p8_3041l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3120_1, c8_3120_2, c8_3120_3, c8_3120_4, c8_3120_5, c8_3120_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3040l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3040l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3040l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3040l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3040l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3040l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3122_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3040l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3122 :
    hubcapFit theRedpart rf8 p8_3040l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3122_1, c8_3122_2, c8_3122_3, c8_3122_4, c8_3122_5, c8_3122_6, c8_3122_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3125r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3125r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3125r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3125r) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3125r) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3125r) (hubSubn 8 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3126_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3125r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3126 :
    hubcapFit theRedpart rf8 p8_3125r
    (Hubcap.one 0 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 1 3 5 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3126_1, c8_3126_2, c8_3126_3, c8_3126_4, c8_3126_5, c8_3126_6, c8_3126_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3125l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3125l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3125l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3125l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3127_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3125l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3127 :
    hubcapFit theRedpart rf8 p8_3125l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3127_1, c8_3127_2, c8_3127_3, c8_3127_4, c8_3127_5, c8_3127_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2744l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_2744l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2744l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2744l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3129_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2744l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3129 :
    hubcapFit theRedpart rf8 p8_2744l
    (Hubcap.one 4 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3129_1, c8_3129_2, c8_3129_3, c8_3129_4, c8_3129_5, c8_3129_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2743l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2743l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2743l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2743l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3131_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2743l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3131 :
    hubcapFit theRedpart rf8 p8_2743l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3131_1, c8_3131_2, c8_3131_3, c8_3131_4, c8_3131_5, c8_3131_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2742l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_2742l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2742l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2742l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3132_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2742l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3132 :
    hubcapFit theRedpart rf8 p8_2742l
    (Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3132_1, c8_3132_2, c8_3132_3, c8_3132_4, c8_3132_5, c8_3132_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_2741l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_2741l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_2741l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_2741l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_2741l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3134_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_2741l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3134 :
    hubcapFit theRedpart rf8 p8_2741l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3134_1, c8_3134_2, c8_3134_3, c8_3134_4, c8_3134_5, c8_3134_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3152r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3152r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3152r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3152r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3152r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3152r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3152r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3153_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3152r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3153 :
    hubcapFit theRedpart rf8 p8_3152r
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3153_1, c8_3153_2, c8_3153_3, c8_3153_4, c8_3153_5, c8_3153_6, c8_3153_7, c8_3153_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3152l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3152l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3154_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3152l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3154 :
    hubcapFit theRedpart rf8 p8_3152l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3154_1, c8_3154_2, c8_3154_3, c8_3154_4, c8_3154_5, c8_3154_6, c8_3154_7]

end FourColor

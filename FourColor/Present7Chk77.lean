import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 77 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4125_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4118l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4125_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4118l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4125_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4118l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4125_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4118l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4125_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4118l) (hubSubn 7 6 5) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4125 :
    hubcapFit theRedpart rf7 p7_4118l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.two 2 4 2 <|
     Hubcap.two 5 6 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4125_1, c7_4125_2, c7_4125_3, c7_4125_4, c7_4125_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4127r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4127r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4127r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4127r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4127r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4127r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4128_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4127r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4128 :
    hubcapFit theRedpart rf7 p7_4127r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4128_1, c7_4128_2, c7_4128_3, c7_4128_4, c7_4128_5, c7_4128_6, c7_4128_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4127l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4127l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4127l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4127l) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4129_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4127l) (hubSubn 7 6 5) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4129 :
    hubcapFit theRedpart rf7 p7_4127l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-2) <|
     Hubcap.two 5 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4129_1, c7_4129_2, c7_4129_3, c7_4129_4, c7_4129_5, c7_4129_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4142r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4142r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4142r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4142r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4142r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4142r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4143_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4142r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4143 :
    hubcapFit theRedpart rf7 p7_4142r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4143_1, c7_4143_2, c7_4143_3, c7_4143_4, c7_4143_5, c7_4143_6, c7_4143_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4145r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4145r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4145r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4145r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4145r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4145r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4146_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4145r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4146 :
    hubcapFit theRedpart rf7 p7_4145r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4146_1, c7_4146_2, c7_4146_3, c7_4146_4, c7_4146_5, c7_4146_6, c7_4146_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4145l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4145l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4145l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4145l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4145l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4145l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4147_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4145l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4147 :
    hubcapFit theRedpart rf7 p7_4145l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4147_1, c7_4147_2, c7_4147_3, c7_4147_4, c7_4147_5, c7_4147_6, c7_4147_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4149_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4149_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4140l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4149_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4140l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4149_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4140l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4149_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4140l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4149 :
    hubcapFit theRedpart rf7 p7_4140l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4149_1, c7_4149_2, c7_4149_3, c7_4149_4, c7_4149_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4154r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4154r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4154r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4154r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4154r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4154r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4155_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4154r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4155 :
    hubcapFit theRedpart rf7 p7_4154r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4155_1, c7_4155_2, c7_4155_3, c7_4155_4, c7_4155_5, c7_4155_6, c7_4155_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4154l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4154l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4154l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4154l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4154l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4154l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4156_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4154l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4156 :
    hubcapFit theRedpart rf7 p7_4154l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4156_1, c7_4156_2, c7_4156_3, c7_4156_4, c7_4156_5, c7_4156_6, c7_4156_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4153l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4153l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4153l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4153l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4158_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4153l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4158 :
    hubcapFit theRedpart rf7 p7_4153l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4158_1, c7_4158_2, c7_4158_3, c7_4158_4, c7_4158_5, c7_4158_6, c7_4158_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4152l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4152l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4152l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4152l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4152l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4160_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4152l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4160 :
    hubcapFit theRedpart rf7 p7_4152l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4160_1, c7_4160_2, c7_4160_3, c7_4160_4, c7_4160_5, c7_4160_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4165r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4165r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4165r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4165r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4165r) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4166_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4165r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4166 :
    hubcapFit theRedpart rf7 p7_4165r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4166_1, c7_4166_2, c7_4166_3, c7_4166_4, c7_4166_5, c7_4166_6, c7_4166_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4165l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4165l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4165l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4165l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4165l) (-1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4167_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4165l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4167 :
    hubcapFit theRedpart rf7 p7_4165l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-1) <|
     Hubcap.one 5 (-1) <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4167_1, c7_4167_2, c7_4167_3, c7_4167_4, c7_4167_5, c7_4167_6, c7_4167_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4164l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4164l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4164l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4164l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4164l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4164l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4169_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4164l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4169 :
    hubcapFit theRedpart rf7 p7_4164l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4169_1, c7_4169_2, c7_4169_3, c7_4169_4, c7_4169_5, c7_4169_6, c7_4169_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4163l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4163l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4163l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4163l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4163l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4171_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4163l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4171 :
    hubcapFit theRedpart rf7 p7_4163l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4171_1, c7_4171_2, c7_4171_3, c7_4171_4, c7_4171_5, c7_4171_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4172_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4162l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4172_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4162l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4172_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4162l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4172_4 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4162l) (hubSubn 7 5 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4172_5 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4162l) (hubSubn 7 4 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4172 :
    hubcapFit theRedpart rf7 p7_4162l
    (Hubcap.one 0 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 5 3 <|
     Hubcap.two 2 4 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4172_1, c7_4172_2, c7_4172_3, c7_4172_4, c7_4172_5]

end FourColor

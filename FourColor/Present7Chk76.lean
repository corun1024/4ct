import FourColor.Present7Defs
import FourColor.TheQuizTree

/-!
Translated from `present7.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 76 of the arity 7 presentation

One of 113 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4067l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4067l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4067l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4067l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4067l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4074_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4067l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4074 :
    hubcapFit theRedpart rf7 p7_4067l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4074_1, c7_4074_2, c7_4074_3, c7_4074_4, c7_4074_5, c7_4074_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4066l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4066l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4066l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4066l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4066l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4076_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4066l) (hubSubn 7 6 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4076 :
    hubcapFit theRedpart rf7 p7_4066l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4076_1, c7_4076_2, c7_4076_3, c7_4076_4, c7_4076_5, c7_4076_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4065l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4065l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4065l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4065l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4065l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4077_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4065l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4077 :
    hubcapFit theRedpart rf7 p7_4065l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4077_1, c7_4077_2, c7_4077_3, c7_4077_4, c7_4077_5, c7_4077_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4064l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4064l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4064l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4064l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4064l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4079_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4064l) (hubSubn 7 3 1) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4079 :
    hubcapFit theRedpart rf7 p7_4064l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 3 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4079_1, c7_4079_2, c7_4079_3, c7_4079_4, c7_4079_5, c7_4079_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4086r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4086r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4086r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4086r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4086r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4087_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4086r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4087 :
    hubcapFit theRedpart rf7 p7_4086r
    (Hubcap.one 0 2 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4087_1, c7_4087_2, c7_4087_3, c7_4087_4, c7_4087_5, c7_4087_6, c7_4087_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4086l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4086l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4086l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4088_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4086l) (hubSubn 7 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4088 :
    hubcapFit theRedpart rf7 p7_4086l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 2 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4088_1, c7_4088_2, c7_4088_3, c7_4088_4, c7_4088_5, c7_4088_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4085l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4085l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4085l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4085l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4085l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4090_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4085l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4090 :
    hubcapFit theRedpart rf7 p7_4085l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4090_1, c7_4090_2, c7_4090_3, c7_4090_4, c7_4090_5, c7_4090_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4083l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4083l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4092_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4083l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4092 :
    hubcapFit theRedpart rf7 p7_4083l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4092_1, c7_4092_2, c7_4092_3, c7_4092_4, c7_4092_5, c7_4092_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4082l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4082l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4082l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4082l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4082l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4093_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4082l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4093 :
    hubcapFit theRedpart rf7 p7_4082l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4093_1, c7_4093_2, c7_4093_3, c7_4093_4, c7_4093_5, c7_4093_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4081l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4081l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4081l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4095_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4081l) (hubSubn 7 6 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4095 :
    hubcapFit theRedpart rf7 p7_4081l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4095_1, c7_4095_2, c7_4095_3, c7_4095_4, c7_4095_5, c7_4095_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4061l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4061l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4061l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4061l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4097_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4061l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4097 :
    hubcapFit theRedpart rf7 p7_4061l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4097_1, c7_4097_2, c7_4097_3, c7_4097_4, c7_4097_5, c7_4097_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4060l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4060l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4060l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4060l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4098_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4060l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4098 :
    hubcapFit theRedpart rf7 p7_4060l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4098_1, c7_4098_2, c7_4098_3, c7_4098_4, c7_4098_5, c7_4098_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4059l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4059l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4059l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4100_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4059l) (hubSubn 7 6 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4100 :
    hubcapFit theRedpart rf7 p7_4059l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.two 1 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4100_1, c7_4100_2, c7_4100_3, c7_4100_4, c7_4100_5, c7_4100_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4058l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4058l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4058l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4058l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4058l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4058l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4101_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4058l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4101 :
    hubcapFit theRedpart rf7 p7_4058l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 0 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4101_1, c7_4101_2, c7_4101_3, c7_4101_4, c7_4101_5, c7_4101_6, c7_4101_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_3996l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_3996l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_3996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_3996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_3996l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4103_6 :
    check2Dbound2 theRedpart rf7
      (hubcapRot 7 1 p7_3996l) (hubSubn 7 3 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4103 :
    hubcapFit theRedpart rf7 p7_3996l
    (Hubcap.one 0 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 0 <|
     Hubcap.two 1 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4103_1, c7_4103_2, c7_4103_3, c7_4103_4, c7_4103_5, c7_4103_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4121r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4121r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4121r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4121r) (-2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4121r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4122_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4121r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4122 :
    hubcapFit theRedpart rf7 p7_4121r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 4 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 (-2) <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4122_1, c7_4122_2, c7_4122_3, c7_4122_4, c7_4122_5, c7_4122_6, c7_4122_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_1 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 0 p7_4121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_2 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 1 p7_4121l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_3 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 2 p7_4121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_4 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 3 p7_4121l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_5 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 4 p7_4121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_6 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 5 p7_4121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c7_4123_7 :
    checkDbound2 theRedpart rf7
      (hubcapRot 7 6 p7_4121l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f7_4123 :
    hubcapFit theRedpart rf7 p7_4121l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 0 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 1 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c7_4123_1, c7_4123_2, c7_4123_3, c7_4123_4, c7_4123_5, c7_4123_6, c7_4123_7]

end FourColor

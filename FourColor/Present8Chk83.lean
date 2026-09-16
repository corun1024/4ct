import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 83 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4146l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4146l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4146l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4146l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4146l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4146l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4158_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4146l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4158 :
    hubcapFit theRedpart rf8 p8_4146l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4158_1, c8_4158_2, c8_4158_3, c8_4158_4, c8_4158_5, c8_4158_6, c8_4158_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4144l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4144l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4144l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4144l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4144l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4160_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4144l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4160 :
    hubcapFit theRedpart rf8 p8_4144l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 1 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4160_1, c8_4160_2, c8_4160_3, c8_4160_4, c8_4160_5, c8_4160_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4143l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4143l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4143l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4143l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4143l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4162_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4143l) (hubSubn 8 7 5) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4162 :
    hubcapFit theRedpart rf8 p8_4143l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 4 1 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4162_1, c8_4162_2, c8_4162_3, c8_4162_4, c8_4162_5, c8_4162_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4140l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4140l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4140l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4140l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4140l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4164_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4140l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4164 :
    hubcapFit theRedpart rf8 p8_4140l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4164_1, c8_4164_2, c8_4164_3, c8_4164_4, c8_4164_5, c8_4164_6, c8_4164_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4139l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4139l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4139l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4139l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4139l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4139l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4166_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4139l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4166 :
    hubcapFit theRedpart rf8 p8_4139l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4166_1, c8_4166_2, c8_4166_3, c8_4166_4, c8_4166_5, c8_4166_6, c8_4166_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4097l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4097l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4097l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4097l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4097l) (hubSubn 8 2 1) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4169_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4097l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4169 :
    hubcapFit theRedpart rf8 p8_4097l
    (Hubcap.one 0 5 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 2 6 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4169_1, c8_4169_2, c8_4169_3, c8_4169_4, c8_4169_5, c8_4169_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4182r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4182r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4183_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4182r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4183 :
    hubcapFit theRedpart rf8 p8_4182r
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4183_1, c8_4183_2, c8_4183_3, c8_4183_4, c8_4183_5, c8_4183_6, c8_4183_7, c8_4183_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4182l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4182l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4182l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4182l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4184_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4182l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4184 :
    hubcapFit theRedpart rf8 p8_4182l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4184_1, c8_4184_2, c8_4184_3, c8_4184_4, c8_4184_5, c8_4184_6, c8_4184_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4181l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4181l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4186_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4181l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4186 :
    hubcapFit theRedpart rf8 p8_4181l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4186_1, c8_4186_2, c8_4186_3, c8_4186_4, c8_4186_5, c8_4186_6, c8_4186_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4179l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4179l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4179l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4179l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4179l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4188_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4179l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4188 :
    hubcapFit theRedpart rf8 p8_4179l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4188_1, c8_4188_2, c8_4188_3, c8_4188_4, c8_4188_5, c8_4188_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4178l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4178l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4178l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4190_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4178l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4190 :
    hubcapFit theRedpart rf8 p8_4178l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4190_1, c8_4190_2, c8_4190_3, c8_4190_4, c8_4190_5, c8_4190_6, c8_4190_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4177l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4177l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4177l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4177l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4177l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4192_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4177l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4192 :
    hubcapFit theRedpart rf8 p8_4177l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4192_1, c8_4192_2, c8_4192_3, c8_4192_4, c8_4192_5, c8_4192_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4176l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4176l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4176l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4176l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4193_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4176l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4193 :
    hubcapFit theRedpart rf8 p8_4176l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4193_1, c8_4193_2, c8_4193_3, c8_4193_4, c8_4193_5, c8_4193_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4195_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4175l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4195_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4175l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4195_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4175l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4195_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4175l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4195_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4175l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4195 :
    hubcapFit theRedpart rf8 p8_4175l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 6 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4195_1, c8_4195_2, c8_4195_3, c8_4195_4, c8_4195_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4174l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4174l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4174l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4174l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4174l) (hubSubn 8 3 2) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4196_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4174l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4196 :
    hubcapFit theRedpart rf8 p8_4174l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 2 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4196_1, c8_4196_2, c8_4196_3, c8_4196_4, c8_4196_5, c8_4196_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4200r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4200r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4200r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4200r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4200r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4200r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4200r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4201_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4200r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4201 :
    hubcapFit theRedpart rf8 p8_4200r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 1 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4201_1, c8_4201_2, c8_4201_3, c8_4201_4, c8_4201_5, c8_4201_6, c8_4201_7, c8_4201_8]

end FourColor

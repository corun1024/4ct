import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 85 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4265r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4265r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4265r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4265r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4265r) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4266_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4265r) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4266 :
    hubcapFit theRedpart rf8 p8_4265r
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4266_1, c8_4266_2, c8_4266_3, c8_4266_4, c8_4266_5, c8_4266_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4265l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4265l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4265l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4265l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4267_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4265l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4267 :
    hubcapFit theRedpart rf8 p8_4265l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4267_1, c8_4267_2, c8_4267_3, c8_4267_4, c8_4267_5, c8_4267_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4264l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4264l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4264l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4269_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4264l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4269 :
    hubcapFit theRedpart rf8 p8_4264l
    (Hubcap.one 0 2 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4269_1, c8_4269_2, c8_4269_3, c8_4269_4, c8_4269_5, c8_4269_6, c8_4269_7, c8_4269_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4263l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4263l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4263l) (hubSubn 8 2 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4271_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4263l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4271 :
    hubcapFit theRedpart rf8 p8_4263l
    (Hubcap.one 1 2 <|
     Hubcap.one 3 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4271_1, c8_4271_2, c8_4271_3, c8_4271_4, c8_4271_5, c8_4271_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4232l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4232l) (hubSubn 8 7 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4232l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4232l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4232l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4273_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4232l) (hubSubn 8 3 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4273 :
    hubcapFit theRedpart rf8 p8_4232l
    (Hubcap.one 6 3 <|
     Hubcap.two 2 7 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 3 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4273_1, c8_4273_2, c8_4273_3, c8_4273_4, c8_4273_5, c8_4273_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4231l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4231l) (hubSubn 8 3 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4231l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4231l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4231l) (hubSubn 8 7 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4275_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4231l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4275 :
    hubcapFit theRedpart rf8 p8_4231l
    (Hubcap.one 6 3 <|
     Hubcap.two 0 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 1 7 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4275_1, c8_4275_2, c8_4275_3, c8_4275_4, c8_4275_5, c8_4275_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4230l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4230l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4230l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4230l) (hubSubn 8 3 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4230l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4230l) (hubSubn 8 7 2) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4276_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4230l) (hubSubn 8 7 3) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4276 :
    hubcapFit theRedpart rf8 p8_4230l
    (Hubcap.one 6 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 3 6 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 2 7 7 <|
     Hubcap.two 3 7 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4276_1, c8_4276_2, c8_4276_3, c8_4276_4, c8_4276_5, c8_4276_6, c8_4276_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4229l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4229l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4229l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4229l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4229l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4278_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4229l) (hubSubn 8 7 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4278 :
    hubcapFit theRedpart rf8 p8_4229l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4278_1, c8_4278_2, c8_4278_3, c8_4278_4, c8_4278_5, c8_4278_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4290r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4290r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4290r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4290r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4290r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4290r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4291_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4290r) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4291 :
    hubcapFit theRedpart rf8 p8_4290r
    (Hubcap.one 1 1 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4291_1, c8_4291_2, c8_4291_3, c8_4291_4, c8_4291_5, c8_4291_6, c8_4291_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4290l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4290l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4290l) (hubSubn 8 1 0) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4290l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4292_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4290l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4292 :
    hubcapFit theRedpart rf8 p8_4290l
    (Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 4 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4292_1, c8_4292_2, c8_4292_3, c8_4292_4, c8_4292_5, c8_4292_6, c8_4292_7, c8_4292_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4288l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4288l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4288l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4288l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4288l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4288l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4294_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4288l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4294 :
    hubcapFit theRedpart rf8 p8_4288l
    (Hubcap.one 1 0 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 2 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4294_1, c8_4294_2, c8_4294_3, c8_4294_4, c8_4294_5, c8_4294_6, c8_4294_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4285l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4285l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4285l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4296_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4285l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4296 :
    hubcapFit theRedpart rf8 p8_4285l
    (Hubcap.one 0 4 <|
     Hubcap.one 3 3 <|
     Hubcap.one 4 3 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4296_1, c8_4296_2, c8_4296_3, c8_4296_4, c8_4296_5, c8_4296_6, c8_4296_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4283l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4283l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4283l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4283l) (hubSubn 8 2 0) 7
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4298_8 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4283l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4298 :
    hubcapFit theRedpart rf8 p8_4283l
    (Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 7 <|
     Hubcap.two 1 2 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4298_1, c8_4298_2, c8_4298_3, c8_4298_4, c8_4298_5, c8_4298_6, c8_4298_7, c8_4298_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4282l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4282l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4282l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4282l) (hubSubn 8 2 1) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4300_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4282l) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4300 :
    hubcapFit theRedpart rf8 p8_4282l
    (Hubcap.one 0 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 1 2 5 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4300_1, c8_4300_2, c8_4300_3, c8_4300_4, c8_4300_5, c8_4300_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4301_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4281l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4301_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4281l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4301_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4281l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4301_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4281l) (hubSubn 8 7 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4301_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4281l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4301 :
    hubcapFit theRedpart rf8 p8_4281l
    (Hubcap.one 4 2 <|
     Hubcap.one 6 3 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 2 7 6 <|
     Hubcap.two 3 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4301_1, c8_4301_2, c8_4301_3, c8_4301_4, c8_4301_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4280l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_2 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4280l) (hubSubn 8 5 3) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4280l) (hubSubn 8 7 4) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4280l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4280l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4303_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4280l) (hubSubn 8 2 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4303 :
    hubcapFit theRedpart rf8 p8_4280l
    (Hubcap.one 6 3 <|
     Hubcap.two 3 5 4 <|
     Hubcap.two 4 7 6 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 1 2 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4303_1, c8_4303_2, c8_4303_3, c8_4303_4, c8_4303_5, c8_4303_6]

end FourColor

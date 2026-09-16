import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 78 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3625l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3625l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3625l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3625l) (hubSubn 8 1 0) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3915_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3625l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3915 :
    hubcapFit theRedpart rf8 p8_3625l
    (Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 5 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3915_1, c8_3915_2, c8_3915_3, c8_3915_4, c8_3915_5, c8_3915_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3624l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3624l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3624l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3624l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3916_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3624l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3916 :
    hubcapFit theRedpart rf8 p8_3624l
    (Hubcap.one 0 3 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 0 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3916_1, c8_3916_2, c8_3916_3, c8_3916_4, c8_3916_5, c8_3916_6, c8_3916_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3931r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3931r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3931r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3931r) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3931r) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3931r) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3932_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3931r) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3932 :
    hubcapFit theRedpart rf8 p8_3931r
    (Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3932_1, c8_3932_2, c8_3932_3, c8_3932_4, c8_3932_5, c8_3932_6, c8_3932_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3931l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3931l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3931l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3931l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3931l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3933_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3931l) (hubSubn 8 4 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3933 :
    hubcapFit theRedpart rf8 p8_3931l
    (Hubcap.one 3 2 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 4 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3933_1, c8_3933_2, c8_3933_3, c8_3933_4, c8_3933_5, c8_3933_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3930l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3930l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3930l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3930l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3930l) (hubSubn 8 4 1) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3935_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3930l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3935 :
    hubcapFit theRedpart rf8 p8_3930l
    (Hubcap.one 0 0 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 1 4 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3935_1, c8_3935_2, c8_3935_3, c8_3935_4, c8_3935_5, c8_3935_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3936_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3929l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3936_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3929l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3936_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3929l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3936_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3929l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3936_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3929l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3936 :
    hubcapFit theRedpart rf8 p8_3929l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3936_1, c8_3936_2, c8_3936_3, c8_3936_4, c8_3936_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3944r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3944r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3944r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3944r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3944r) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3945_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3944r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3945 :
    hubcapFit theRedpart rf8 p8_3944r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3945_1, c8_3945_2, c8_3945_3, c8_3945_4, c8_3945_5, c8_3945_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3944l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3944l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3944l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3944l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3944l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3944l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3946_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3944l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3946 :
    hubcapFit theRedpart rf8 p8_3944l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3946_1, c8_3946_2, c8_3946_3, c8_3946_4, c8_3946_5, c8_3946_6, c8_3946_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3941l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3941l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3941l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3941l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3941l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3948_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3941l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3948 :
    hubcapFit theRedpart rf8 p8_3941l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3948_1, c8_3948_2, c8_3948_3, c8_3948_4, c8_3948_5, c8_3948_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3940l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3940l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3940l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3940l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3940l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3950_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3940l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3950 :
    hubcapFit theRedpart rf8 p8_3940l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3950_1, c8_3950_2, c8_3950_3, c8_3950_4, c8_3950_5, c8_3950_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3951_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3951_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3939l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3951_3 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3939l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3951_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3939l) (hubSubn 8 3 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3951_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3939l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3951 :
    hubcapFit theRedpart rf8 p8_3939l
    (Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 2 3 5 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3951_1, c8_3951_2, c8_3951_3, c8_3951_4, c8_3951_5]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3938l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3938l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3938l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3938l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3953_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3938l) (hubSubn 8 5 4) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3953 :
    hubcapFit theRedpart rf8 p8_3938l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3953_1, c8_3953_2, c8_3953_3, c8_3953_4, c8_3953_5, c8_3953_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3927l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3927l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3927l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3927l) (hubSubn 8 1 0) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3955_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3927l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3955 :
    hubcapFit theRedpart rf8 p8_3927l
    (Hubcap.one 2 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 1 3 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3955_1, c8_3955_2, c8_3955_3, c8_3955_4, c8_3955_5, c8_3955_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3926l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3926l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3926l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3926l) (hubSubn 8 3 2) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3956_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3926l) (hubSubn 8 5 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3956 :
    hubcapFit theRedpart rf8 p8_3926l
    (Hubcap.one 0 1 <|
     Hubcap.one 1 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 4 <|
     Hubcap.two 4 5 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3956_1, c8_3956_2, c8_3956_3, c8_3956_4, c8_3956_5, c8_3956_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3971r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3971r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3971r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3971r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3972_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3971r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3972 :
    hubcapFit theRedpart rf8 p8_3971r
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 4 <|
     Hubcap.one 4 1 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3972_1, c8_3972_2, c8_3972_3, c8_3972_4, c8_3972_5, c8_3972_6, c8_3972_7, c8_3972_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3971l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3971l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3971l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3971l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3973_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_3971l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3973 :
    hubcapFit theRedpart rf8 p8_3971l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 4 <|
     Hubcap.one 5 2 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3973_1, c8_3973_2, c8_3973_3, c8_3973_4, c8_3973_5, c8_3973_6, c8_3973_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_3970l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_3970l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_3970l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_3970l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_3970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_3970l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_3975_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_3970l) (hubSubn 8 3 2) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_3975 :
    hubcapFit theRedpart rf8 p8_3970l
    (Hubcap.one 0 0 <|
     Hubcap.one 1 3 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 6 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_3975_1, c8_3975_2, c8_3975_3, c8_3975_4, c8_3975_5, c8_3975_6, c8_3975_7]

end FourColor

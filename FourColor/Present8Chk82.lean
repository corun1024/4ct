import FourColor.Present8Defs
import FourColor.TheQuizTree

/-!
Translated from `present8.v` of the Coq proof by G. Gonthier and B. Werner
(rocq-community/fourcolor, CeCILL-B licence); see the README.
-/

/-! # Hubcap checks 82 of the arity 8 presentation

One of 110 independent modules of hubcap checks; every hubcap's checks
and the theorem combining them are in the same module, so the modules build in
parallel. -/

set_option Elab.async false

namespace FourColor

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4105l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4105l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4105l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_4 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4105l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4105l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4105l) (hubSubn 8 4 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4110_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4105l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4110 :
    hubcapFit theRedpart rf8 p8_4105l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 2 4 3 <|
     Hubcap.two 3 4 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4110_1, c8_4110_2, c8_4110_3, c8_4110_4, c8_4110_5, c8_4110_6, c8_4110_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4113r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4113r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4113r) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4113r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4113r) (hubSubn 8 6 0) 8
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4114_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4113r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4114 :
    hubcapFit theRedpart rf8 p8_4113r
    (Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 6 8 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4114_1, c8_4114_2, c8_4114_3, c8_4114_4, c8_4114_5, c8_4114_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4113l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4113l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4113l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4113l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4113l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4113l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4115_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4113l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4115 :
    hubcapFit theRedpart rf8 p8_4113l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 1 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4115_1, c8_4115_2, c8_4115_3, c8_4115_4, c8_4115_5, c8_4115_6, c8_4115_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4112l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4112l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4112l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4112l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4112l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_7 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4117_8 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4112l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4117 :
    hubcapFit theRedpart rf8 p8_4112l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 2 <|
     Hubcap.one 5 0 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4117_1, c8_4117_2, c8_4117_3, c8_4117_4, c8_4117_5, c8_4117_6, c8_4117_7, c8_4117_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4103l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4103l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4103l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4103l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4103l) (hubSubn 8 6 4) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4119_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4103l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4119 :
    hubcapFit theRedpart rf8 p8_4103l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 0 <|
     Hubcap.two 4 6 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4119_1, c8_4119_2, c8_4119_3, c8_4119_4, c8_4119_5, c8_4119_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4126r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4126r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4126r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4126r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4126r) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4126r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4127_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4126r) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4127 :
    hubcapFit theRedpart rf8 p8_4126r
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4127_1, c8_4127_2, c8_4127_3, c8_4127_4, c8_4127_5, c8_4127_6, c8_4127_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4126l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4126l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4126l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4126l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4126l) (hubSubn 8 4 3) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4128_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4126l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4128 :
    hubcapFit theRedpart rf8 p8_4126l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 2 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4128_1, c8_4128_2, c8_4128_3, c8_4128_4, c8_4128_5, c8_4128_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4125l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4125l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4125l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4130_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4125l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4130 :
    hubcapFit theRedpart rf8 p8_4125l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 2 <|
     Hubcap.one 3 2 <|
     Hubcap.one 4 2 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4130_1, c8_4130_2, c8_4130_3, c8_4130_4, c8_4130_5, c8_4130_6, c8_4130_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4123l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4123l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4123l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4123l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4123l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4132_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4123l) (hubSubn 8 6 5) 4
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4132 :
    hubcapFit theRedpart rf8 p8_4123l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 4 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4132_1, c8_4132_2, c8_4132_3, c8_4132_4, c8_4132_5, c8_4132_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4122l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4122l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_5 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4122l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_6 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4122l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4134_7 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4122l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4134 :
    hubcapFit theRedpart rf8 p8_4122l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 2 4 <|
     Hubcap.one 3 0 <|
     Hubcap.one 4 1 <|
     Hubcap.one 7 4 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4134_1, c8_4134_2, c8_4134_3, c8_4134_4, c8_4134_5, c8_4134_6, c8_4134_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4121l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4121l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4121l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4121l) (hubSubn 8 4 2) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4136_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4121l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4136 :
    hubcapFit theRedpart rf8 p8_4121l
    (Hubcap.one 0 4 <|
     Hubcap.one 1 2 <|
     Hubcap.one 3 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 4 5 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4136_1, c8_4136_2, c8_4136_3, c8_4136_4, c8_4136_5, c8_4136_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4099l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4099l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4099l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4099l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4099l) (hubSubn 8 4 3) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4138_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4099l) (hubSubn 8 6 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4138 :
    hubcapFit theRedpart rf8 p8_4099l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 0 <|
     Hubcap.one 7 4 <|
     Hubcap.two 3 4 3 <|
     Hubcap.two 5 6 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4138_1, c8_4138_2, c8_4138_3, c8_4138_4, c8_4138_5, c8_4138_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4151r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4151r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4151r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4151r) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4151r) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4152_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4151r) (hubSubn 8 5 4) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4152 :
    hubcapFit theRedpart rf8 p8_4151r
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 3 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 3 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4152_1, c8_4152_2, c8_4152_3, c8_4152_4, c8_4152_5, c8_4152_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4150l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4150l) 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4150l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4150l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4150l) (hubSubn 8 2 0) 6
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4153_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4150l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4153 :
    hubcapFit theRedpart rf8 p8_4150l
    (Hubcap.one 1 3 <|
     Hubcap.one 3 1 <|
     Hubcap.one 6 4 <|
     Hubcap.one 7 4 <|
     Hubcap.two 0 2 6 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4153_1, c8_4153_2, c8_4153_3, c8_4153_4, c8_4153_5, c8_4153_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4149l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 6 p8_4149l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 7 p8_4149l) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4149l) (hubSubn 8 3 2) 3
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4155_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4149l) (hubSubn 8 5 4) 2
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4155 :
    hubcapFit theRedpart rf8 p8_4149l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 6 3 <|
     Hubcap.one 7 4 <|
     Hubcap.two 2 3 3 <|
     Hubcap.two 4 5 2 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4155_1, c8_4155_2, c8_4155_3, c8_4155_4, c8_4155_5, c8_4155_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_1 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 0 p8_4147l) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_2 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 1 p8_4147l) 3 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_3 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 2 p8_4147l) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_4 :
    checkDbound2 theRedpart rf8
      (hubcapRot 8 4 p8_4147l) 0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_5 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 3 p8_4147l) (hubSubn 8 6 3) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem c8_4157_6 :
    check2Dbound2 theRedpart rf8
      (hubcapRot 8 5 p8_4147l) (hubSubn 8 7 5) 5
      = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Every side condition is a kernel computation over one of the parts above.
theorem f8_4157 :
    hubcapFit theRedpart rf8 p8_4147l
    (Hubcap.one 0 5 <|
     Hubcap.one 1 3 <|
     Hubcap.one 2 2 <|
     Hubcap.one 4 0 <|
     Hubcap.two 3 6 5 <|
     Hubcap.two 5 7 5 <|
     Hubcap.nil) = true := by
  simp [hubcapFit, c8_4157_1, c8_4157_2, c8_4157_3, c8_4157_4, c8_4157_5, c8_4157_6]

end FourColor
